-- Prove2me | solution 1 for GeometryOfGraphs.Cube.corollary_5_12
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:11:58.467067+00:00
-- url     : https://prove2.me/submissions/38b50097-5291-41e3-a247-48655078cdbc

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension
import Definitions.Def_GeometryOfGraphs_Cube_Hypercube
open GeometryOfGraphs.Cube

namespace Paper23.Cube

theorem cube_walk {m : ℕ} (x y : Fin m → Bool) :
    ∃ p : (hypercube m).Walk x y, p.length = hammingDist x y := by
  classical
  generalize hk : hammingDist x y = k
  induction k using Nat.strong_induction_on generalizing x y with
  | h k ih =>
    by_cases hxy : x = y
    · subst y
      exact ⟨.nil, by simpa using hk⟩
    have hn : (Finset.univ.filter (fun i => x i ≠ y i)).Nonempty := by
      apply Finset.card_pos.mp
      exact hammingDist_pos.mpr hxy
    obtain ⟨i, hi⟩ := hn
    have hdiff : x i ≠ y i := (Finset.mem_filter.mp hi).2
    let z := Function.update x i (y i)
    have hset : Finset.univ.filter (fun j => z j ≠ y j) =
        (Finset.univ.filter (fun j => x j ≠ y j)).erase i := by
      ext j
      by_cases hji : j = i
      · subst j; simp [z]
      · simp [z, Function.update_of_ne hji, hji]
    have hdist : hammingDist z y = k - 1 := by
      unfold hammingDist
      rw [hset, Finset.card_erase_of_mem hi]
      exact congrArg (fun q => q - 1) hk
    have hkpos : 0 < k := hk ▸ hammingDist_pos.mpr hxy
    obtain ⟨p, hp⟩ := ih (k - 1) (by omega) z y hdist
    have hadj : (hypercube m).Adj x z := by
      change hammingDist x z = 1
      have hs : Finset.univ.filter (fun j => x j ≠ z j) = {i} := by
        ext j
        by_cases hji : j = i
        · subst j; simp [z, hdiff]
        · simp [z, Function.update_of_ne hji, hji]
      simp [hammingDist, hs]
    refine ⟨.cons hadj p, ?_⟩
    simp only [SimpleGraph.Walk.length_cons, hp]
    omega

theorem cube_dist {m : ℕ} (x y : Fin m → Bool) :
    (hypercube m).dist x y = hammingDist x y := by
  obtain ⟨p, hp⟩ := cube_walk x y
  apply le_antisymm
  · exact hp ▸ (hypercube m).dist_le p
  · obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    have hlow {a b : Fin m → Bool} (w : (hypercube m).Walk a b) :
        hammingDist a b ≤ w.length := by
      induction w with
      | nil => simp
      | @cons a b c hab w ih =>
        have h := hammingDist_triangle a b c
        have hadj : hammingDist a b = 1 := hab
        simp only [SimpleGraph.Walk.length_cons]
        omega
    exact hq ▸ hlow q

theorem l1_norm (m : ℕ) :
    GeometryOfGraphs.Clique.IsNormFun (fun v : Fin m → ℝ => ∑ i, |v i|) := by
  classical
  refine ⟨fun v => Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_, ?_, ?_⟩
  · intro v hv
    funext i
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (v j))).mp hv
    exact abs_eq_zero.mp (h i (Finset.mem_univ i))
  · intro a v
    simp [Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  · intro v w
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun _ _ => abs_add_le _ _)

theorem cube_embedding (m : ℕ) : EmbedsIsometrically (hypercube m) m := by
  classical
  let φ : (Fin m → Bool) → Fin m → ℝ := fun x i => if x i then 1 else 0
  refine ⟨(fun v => ∑ i, |v i|), l1_norm m, φ, ?_⟩
  intro x y
  rw [cube_dist]
  change (∑ i, |φ x i - φ y i|) = (hammingDist x y : ℝ)
  unfold hammingDist
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> simp [φ, hx, hy]

theorem cube_upper (m : ℕ) : isoDim (hypercube m) ≤ m :=
  Nat.sInf_le (cube_embedding m)

end Paper23.Cube

open GeometryOfGraphs.Cube

namespace Paper23.Cube

theorem supporting {d : ℕ} (N : (Fin d → ℝ) → ℝ)
    (hN : GeometryOfGraphs.Clique.IsNormFun N) (x : Fin d → ℝ) (hx : x ≠ 0) :
    ∃ f : (Fin d → ℝ) →ₗ[ℝ] ℝ, f x = N x ∧ ∀ y, f y ≤ N y := by
  let p : (Fin d → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x (N x) hx
  have hp : ∀ y : p.domain, p y ≤ N y := by
    intro y
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp y.2
    have hy : y = ⟨c • x, by rw [hc]; exact y.2⟩ := Subtype.ext hc.symm
    rw [hy]
    change LinearPMap.mkSpanSingleton x (N x) hx _ ≤ N (c • x)
    simp only [LinearPMap.mkSpanSingleton, LinearPMap.mkSpanSingleton'_apply,
      RingHom.id_apply, smul_eq_mul]
    rw [hN.2.2.1]
    change c * N x ≤ |c| * N x
    exact mul_le_mul_of_nonneg_right (le_abs_self c) (hN.1 x)
  obtain ⟨f, hf, hb⟩ := exists_extension_of_le_sublinear p N
    (fun c hc y => by rw [hN.2.2.1, abs_of_pos hc]) hN.2.2.2 hp
  refine ⟨f, ?_, hb⟩
  have he := hf ⟨x, Submodule.mem_span_singleton_self x⟩
  exact he.trans (LinearPMap.mkSpanSingleton_apply ℝ ℝ hx (N x))

def cubePrefix (m k : ℕ) : Fin m → Bool := fun i => decide (i.val < k)

theorem prefix_hamming {m k l : ℕ} (hk : k ≤ m) (hl : l ≤ m) (hkl : k ≤ l) :
    hammingDist (cubePrefix m k) (cubePrefix m l) = l - k := by
  classical
  let A : Finset (Fin m) := Finset.univ.filter (fun i => i.val < k)
  let B : Finset (Fin m) := Finset.univ.filter (fun i => i.val < l)
  have hAB : A ⊆ B := by
    intro i hi
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  have hs : Finset.univ.filter (fun i => cubePrefix m k i ≠ cubePrefix m l i) = B \ A := by
    ext i
    simp only [cubePrefix, ne_eq, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff, A, B]
    by_cases hik : i.val < k <;> by_cases hil : i.val < l <;> simp_all <;> omega
  unfold hammingDist
  rw [hs, Finset.card_sdiff_of_subset hAB]
  simp only [A, B, Fin.card_filter_val_lt, min_eq_right hk, min_eq_right hl]

theorem complement_hamming {m : ℕ} (x y : Fin m → Bool) :
    hammingDist x y + hammingDist y (fun i => !(x i)) = m := by
  classical
  unfold hammingDist
  have hs : Finset.univ.filter (fun i => y i ≠ !(x i)) =
      Finset.univ.filter (fun i => ¬ (x i ≠ y i)) := by
    ext i
    cases hx : x i <;> cases hy : y i <;> simp [hx, hy]
  rw [hs, Finset.card_filter_add_card_filter_not]
  simp

theorem sign_independent {m d : ℕ} (hm : 0 < m) (v : Fin m → (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ j i, f j (v i) = if j ≤ i then 1 else -1) :
    LinearIndependent ℝ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he (j : Fin m) : ∑ k : Fin m, c k * (if j ≤ k then 1 else -1) = 0 := by
    have h := congrArg (f j) hc
    simpa only [map_sum, map_smul, smul_eq_mul, hf, map_zero] using h
  have hz (j : Fin m) (hj : j.val + 1 < m) : c j = 0 := by
    let j' : Fin m := ⟨j.val + 1, hj⟩
    have hdiff : (∑ k : Fin m, c k * (if j ≤ k then 1 else -1)) -
        (∑ k : Fin m, c k * (if j' ≤ k then 1 else -1)) = 2 * c j := by
      rw [← Finset.sum_sub_distrib]
      have hh : ∀ k : Fin m, c k * (if j ≤ k then 1 else -1) -
          c k * (if j' ≤ k then 1 else -1) = if k = j then 2 * c j else 0 := by
        intro k
        by_cases hkj : k = j
        · subst k
          have hnj : ¬ j' ≤ j := by change ¬ j.val + 1 ≤ j.val; omega
          simp [hnj]; ring
        · have hval : k.val ≠ j.val := by exact fun h => hkj (Fin.ext h)
          by_cases hjk : j ≤ k
          · have hj'k : j' ≤ k := by
              change j.val + 1 ≤ k.val
              change j.val ≤ k.val at hjk
              omega
            simp [hjk, hj'k, hkj]
          · have hj'k : ¬ j' ≤ k := by
              change ¬ j.val + 1 ≤ k.val
              change ¬ j.val ≤ k.val at hjk
              omega
            simp [hjk, hj'k, hkj]
      simp_rw [hh]
      simp
    rw [he j, he j'] at hdiff
    linarith
  by_cases hi : i.val + 1 < m
  · exact hz i hi
  · have hlast : i.val = m - 1 := by omega
    let first : Fin m := ⟨0, hm⟩
    have hsum : (∑ k : Fin m, c k * (if first ≤ k then 1 else -1)) = c i := by
      have hfirst (k : Fin m) : first ≤ k := by change 0 ≤ k.val; omega
      simp only [hfirst, if_true, mul_one]
      apply Finset.sum_eq_single i
      · intro k _ hki
        have : k.val ≠ i.val := fun h => hki (Fin.ext h)
        exact hz k (by omega)
      · simp
    exact hsum ▸ he first

end Paper23.Cube

open GeometryOfGraphs.Cube Paper23.Cube

private theorem prefix_distance {m k l : ℕ} (hk : k ≤ m) (hl : l ≤ m) :
    (hammingDist (cubePrefix m k) (cubePrefix m l) : ℝ) = |(k : ℝ) - (l : ℝ)| := by
  by_cases hkl : k ≤ l
  · have hle : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    rw [prefix_hamming hk hl hkl, Nat.cast_sub hkl, abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  · have hlk : l ≤ k := by omega
    have hle : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
    rw [hammingDist_comm, prefix_hamming hl hk hlk, Nat.cast_sub hlk,
      abs_of_nonneg (sub_nonneg.mpr hle)]

private theorem cube_lower (m : ℕ) (hm : 1 ≤ m) (d : ℕ)
    (hd : EmbedsIsometrically (hypercube m) d) : m ≤ d := by
  classical
  obtain ⟨N, hN, φ, hφ⟩ := hd
  have he (x y : Fin m → Bool) : N (φ x - φ y) = (hammingDist x y : ℝ) := by
    rw [hφ, cube_dist]
  have hs (j : Fin m) : ∃ f : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      f (φ (cubePrefix m j.val) - φ (fun i => !(cubePrefix m j.val i))) = m ∧
      ∀ y, f y ≤ N y := by
    let x := cubePrefix m j.val
    have hdcomp : hammingDist x (fun i => !(x i)) = m := by
      simpa using complement_hamming x x
    have hv : φ x - φ (fun i => !(x i)) ≠ 0 := by
      intro hz
      have hzero : N (0 : Fin d → ℝ) = 0 := by
        have h := hN.2.2.1 (0 : ℝ) (0 : Fin d → ℝ)
        simpa using h
      have hh := he x (fun i => !(x i))
      rw [hz, hzero, hdcomp] at hh
      have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      linarith
    obtain ⟨f, hf, hb⟩ := supporting N hN _ hv
    refine ⟨f, ?_, hb⟩
    simpa [he, hdcomp] using hf
  choose f hfm hfb using hs
  have hvalue (j : Fin m) (y : Fin m → Bool) :
      f j (φ (cubePrefix m j.val) - φ y) =
        (hammingDist (cubePrefix m j.val) y : ℝ) := by
    let x := cubePrefix m j.val
    let z : Fin m → Bool := fun i => !(x i)
    have ha := hfb j (φ x - φ y)
    have hb := hfb j (φ y - φ z)
    rw [he] at ha hb
    have hc := complement_hamming x y
    have hcr : (hammingDist x y : ℝ) + (hammingDist y z : ℝ) = (m : ℝ) := by
      exact_mod_cast hc
    have hf := hfm j
    have hsum : f j (φ x - φ y) + f j (φ y - φ z) = (m : ℝ) := by
      rw [← map_add, sub_add_sub_cancel]
      exact hf
    apply le_antisymm ha
    linarith
  let v : Fin m → Fin d → ℝ := fun i => φ (cubePrefix m i.val) - φ (cubePrefix m (i.val + 1))
  have hv : LinearIndependent ℝ v := by
    apply sign_independent (by omega) v f
    intro j i
    have h₀ := hvalue j (cubePrefix m i.val)
    have h₁ := hvalue j (cubePrefix m (i.val + 1))
    rw [prefix_distance (by omega) (by omega)] at h₀ h₁
    have hcalc : f j (v i) = |(j.val : ℝ) - (i.val + 1 : ℕ)| -
        |(j.val : ℝ) - (i.val : ℝ)| := by
      dsimp [v]
      simp only [map_sub] at h₀ h₁ ⊢
      linarith
    rw [hcalc, Nat.cast_add, Nat.cast_one]
    by_cases hji : j ≤ i
    · have hle : (j.val : ℝ) ≤ i.val := by exact_mod_cast hji
      rw [if_pos hji, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
    · have hle : (i.val : ℝ) + 1 ≤ j.val := by
        have : i.val + 1 ≤ j.val := by change ¬ j.val ≤ i.val at hji; omega
        exact_mod_cast this
      rw [if_neg hji, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring
  simpa using hv.fintype_card_le_finrank

theorem solution (m : ℕ) (hm : 1 ≤ m) : isoDim (hypercube m) = m := by
  apply le_antisymm (cube_upper m)
  have hne : {d : ℕ | EmbedsIsometrically (hypercube m) d}.Nonempty := ⟨m, cube_embedding m⟩
  exact cube_lower m hm _ (Nat.sInf_mem hne)


#print axioms solution

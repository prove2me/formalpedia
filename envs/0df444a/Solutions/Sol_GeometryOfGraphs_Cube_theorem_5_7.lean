-- Prove2me | solution 1 for GeometryOfGraphs.Cube.theorem_5_7
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T03:49:15.864118+00:00
-- url     : https://prove2.me/submissions/79e57f01-6e04-4720-9c13-f41f39e99777

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension
import Definitions.Def_GeometryOfGraphs_Cube_Implements

set_option autoImplicit false

section

namespace GeometryOfGraphs.Cube.CRFresh

end GeometryOfGraphs.Cube.CRFresh
end

section

namespace GeometryOfGraphs.Cube.CRFresh

theorem norm_fun_zero {d : ℕ} {N : (Fin d → ℝ) → ℝ}
    (hN : Clique.IsNormFun N) : N 0 = 0 := by
  simpa using hN.2.2.1 0 (0 : Fin d → ℝ)

theorem norm_fun_neg {d : ℕ} {N : (Fin d → ℝ) → ℝ}
    (hN : Clique.IsNormFun N) (z : Fin d → ℝ) : N (-z) = N z := by
  simpa using hN.2.2.1 (-1) z

theorem exists_norming_linear {d : ℕ} {N : (Fin d → ℝ) → ℝ}
    (hN : Clique.IsNormFun N) (z : Fin d → ℝ) :
    ∃ l : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ y, |l y| ≤ N y) ∧ l z = N z := by
  classical
  by_cases hz : z = 0
  · subst z
    exact ⟨0, by simpa using hN.1, by simp [norm_fun_zero hN]⟩
  let f : (Fin d → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton z (N z) hz
  have hf : ∀ y : f.domain, f y ≤ N y := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    change LinearPMap.mkSpanSingleton' z (N z) _ ⟨a • z, _⟩ ≤ N (a • z)
    rw [LinearPMap.mkSpanSingleton'_apply, hN.2.2.1]
    simpa using mul_le_mul_of_nonneg_right (le_abs_self a) (hN.1 z)
  obtain ⟨l, hl, hle⟩ := exists_extension_of_le_sublinear f N
    (fun a ha y => by rw [hN.2.2.1, abs_of_pos ha]) hN.2.2.2 hf
  refine ⟨l, ?_, ?_⟩
  · intro y
    apply abs_le.mpr
    constructor
    · have hn := hle (-y)
      rw [map_neg, norm_fun_neg hN] at hn
      linarith
    · exact hle y
  · have h := hl ⟨z, Submodule.mem_span_singleton_self z⟩
    exact h.trans (LinearPMap.mkSpanSingleton_apply ℝ ℝ hz (N z))

end GeometryOfGraphs.Cube.CRFresh
end

section

namespace GeometryOfGraphs.Cube.CRFresh

theorem rank_evaluation_le {V : Type*} [Fintype V] {d r : ℕ}
    (F : (Fin d → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (φ : V → (Fin d → ℝ)) :
    (Matrix.of (fun v => F (φ v))).rank ≤ d := by
  classical
  rw [Matrix.rank_eq_finrank_span_row]
  have hs : Submodule.span ℝ (Set.range (fun v => F (φ v))) ≤ LinearMap.range F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact ⟨φ v, rfl⟩
  exact (Submodule.finrank_mono hs).trans (by simpa using F.finrank_range_le)

theorem embeds_implements {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (h : EmbedsIsometrically G d) :
    ∃ (r : ℕ) (M : Matrix V (Fin r) ℝ), Implements G M ∧ M.rank ≤ d := by
  classical
  obtain ⟨N, hN, φ, hφ⟩ := h
  choose l hl hnorm using fun p : V × V => exists_norming_linear hN (φ p.1 - φ p.2)
  let r := Fintype.card (V × V)
  let e : (V × V) ≃ Fin r := Fintype.equivFin (V × V)
  let F : (Fin d → ℝ) →ₗ[ℝ] (Fin r → ℝ) := LinearMap.pi (fun i => l (e.symm i))
  let M : Matrix V (Fin r) ℝ := Matrix.of (fun v => F (φ v))
  refine ⟨r, M, ?_, rank_evaluation_le F φ⟩
  intro u v
  constructor
  · intro k
    change |l (e.symm k) (φ u) - l (e.symm k) (φ v)| ≤ _
    rw [← map_sub]
    exact (hl (e.symm k) (φ u - φ v)).trans_eq (hφ u v)
  · intro _
    refine ⟨e (u, v), ?_⟩
    change |l (e.symm (e (u, v))) (φ u) - l (e.symm (e (u, v))) (φ v)| = _
    rw [e.symm_apply_apply, ← map_sub, hnorm (u, v), abs_of_nonneg (hN.1 _), hφ]

end GeometryOfGraphs.Cube.CRFresh
end

section

namespace GeometryOfGraphs.Cube.CRFresh

lemma normFun_of_linear_injective {d : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (L : (Fin d → ℝ) →ₗ[ℝ] W) (hL : Function.Injective L) :
    GeometryOfGraphs.Clique.IsNormFun (fun z => ‖L z‖) := by
  refine ⟨fun z => norm_nonneg _, ?_, ?_, ?_⟩
  · intro z hz
    apply hL
    simpa only [map_zero] using norm_eq_zero.mp hz
  · intro a z
    change ‖L (a • z)‖ = |a| * ‖L z‖
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  · intro z w
    change ‖L (z + w)‖ ≤ ‖L z‖ + ‖L w‖
    rw [map_add]
    exact norm_add_le _ _

lemma implementing_norm_distance {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (M : Matrix V (Fin r) ℝ) (hM : Implements G M) (i j : V) :
    ‖M i - M j‖ = (G.dist i j : ℝ) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
    intro k
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hM i j).1 k
  · by_cases hij : i = j
    · subst j
      simp
    · obtain ⟨k, hk⟩ := (hM i j).2 hij
      have hh := norm_le_pi_norm (M i - M j) k
      simpa only [Pi.sub_apply, Real.norm_eq_abs, hk] using hh

 theorem implements_embeds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ} (M : Matrix V (Fin r) ℝ) (hM : Implements G M) :
    EmbedsIsometrically G M.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_row]
  let W := Submodule.span ℝ (Set.range M.row)
  let b := Module.finBasis ℝ W
  let L : (Fin (Module.finrank ℝ W) → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  have hL : Function.Injective L :=
    Subtype.val_injective.comp b.equivFun.symm.injective
  have hrow (v : V) : M v ∈ W := Submodule.subset_span ⟨v, rfl⟩
  let φ : V → (Fin (Module.finrank ℝ W) → ℝ) :=
    fun v => b.equivFun ⟨M v, hrow v⟩
  refine ⟨fun z => ‖L z‖, normFun_of_linear_injective L hL, φ, ?_⟩
  intro i j
  have hval (v : V) : L (φ v) = M v := by
    simp [L, φ]
  change ‖L (φ i - φ j)‖ = (G.dist i j : ℝ)
  rw [map_sub, hval, hval]
  exact implementing_norm_distance G M hM i j

end GeometryOfGraphs.Cube.CRFresh
end

section

namespace GeometryOfGraphs.Cube.CRFresh

lemma graph_distance_difference {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (i j w : V) :
    |(G.dist i w : ℝ) - (G.dist j w : ℝ)| ≤ (G.dist i j : ℝ) := by
  have h₁ : (G.dist i w : ℝ) ≤ (G.dist i j : ℝ) + (G.dist j w : ℝ) := by
    exact_mod_cast (hG.dist_triangle (u := i) (v := j) (w := w))
  have h₂ : (G.dist j w : ℝ) ≤ (G.dist i j : ℝ) + (G.dist i w : ℝ) := by
    have hh := hG.dist_triangle (u := j) (v := i) (w := w)
    rw [G.dist_comm (u := j) (v := i)] at hh
    exact_mod_cast hh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

 theorem exists_implements {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ (r : ℕ) (M : Matrix V (Fin r) ℝ), Implements G M := by
  classical
  let e := Fintype.equivFin V
  refine ⟨Fintype.card V, fun v k => (G.dist v (e.symm k) : ℝ), ?_⟩
  intro i j
  constructor
  · intro k
    exact graph_distance_difference G hG i j (e.symm k)
  · intro _
    refine ⟨e j, ?_⟩
    simp only [Equiv.symm_apply_apply, SimpleGraph.dist_self, Nat.cast_zero, sub_zero]
    exact abs_of_nonneg (Nat.cast_nonneg _)

end GeometryOfGraphs.Cube.CRFresh
end

section

namespace GeometryOfGraphs.Cube.CRFresh

lemma nat_sInf_eq_of_mutual_witnesses (A B : Set ℕ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ a ∈ A, ∃ b ∈ B, b ≤ a)
    (hBA : ∀ b ∈ B, ∃ a ∈ A, a ≤ b) : sInf A = sInf B := by
  apply le_antisymm
  · obtain ⟨a, ha, hab⟩ := hBA (sInf B) (Nat.sInf_mem hB)
    exact (Nat.sInf_le ha).trans hab
  · obtain ⟨b, hb, hba⟩ := hAB (sInf A) (Nat.sInf_mem hA)
    exact (Nat.sInf_le hb).trans hba

end GeometryOfGraphs.Cube.CRFresh
end

section

namespace GeometryOfGraphs.Cube.CRFresh

theorem native_theorem_5_7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    isoDim G = sInf {k : ℕ | ∃ (r : ℕ) (M : Matrix V (Fin r) ℝ),
      Implements G M ∧ M.rank = k} := by
  classical
  let A : Set ℕ := {d : ℕ | EmbedsIsometrically G d}
  let B : Set ℕ := {k : ℕ | ∃ (r : ℕ) (M : Matrix V (Fin r) ℝ),
    Implements G M ∧ Matrix.rank M = k}
  obtain ⟨r, M, hM⟩ := exists_implements G hG
  have hA : A.Nonempty := ⟨Matrix.rank M, implements_embeds G M hM⟩
  have hB : B.Nonempty := ⟨Matrix.rank M, r, M, hM, rfl⟩
  change sInf A = sInf B
  apply nat_sInf_eq_of_mutual_witnesses A B hA hB
  · intro d hd
    obtain ⟨r', M', hM', hle⟩ := embeds_implements hd
    exact ⟨Matrix.rank M', ⟨r', M', hM', rfl⟩, hle⟩
  · intro k hk
    obtain ⟨r', M', hM', heq⟩ := hk
    exact ⟨Matrix.rank M', implements_embeds G M' hM', heq.le⟩

end GeometryOfGraphs.Cube.CRFresh
end

open GeometryOfGraphs.Cube

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    isoDim G = sInf {k : ℕ | ∃ (r : ℕ) (M : Matrix V (Fin r) ℝ),
      Implements G M ∧ M.rank = k} := by
  exact CRFresh.native_theorem_5_7 G hG

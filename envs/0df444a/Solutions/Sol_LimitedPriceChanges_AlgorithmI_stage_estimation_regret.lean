-- Prove2me | solution 1 for LimitedPriceChanges.AlgorithmI.stage_estimation_regret
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:23:46.513631+00:00
-- url     : https://prove2.me/submissions/c195645a-7b61-4642-b900-5ab6772571a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm
import Theorems.Thm_LimitedPriceChanges_AlgorithmI_proposition_1

namespace LPCB1Aux

/-- Uniformize a "small positive constant" over a finite index set. -/
theorem uniform_small {ι : Type*} (Y : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ y c c', 0 < c' → c' ≤ c → P y c → P y c')
    (h : ∀ y ∈ Y, ∃ c : ℝ, 0 < c ∧ P y c) : ∃ c : ℝ, 0 < c ∧ ∀ y ∈ Y, P y c := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc, hcs⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨ca, hca, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨min c ca, lt_min hc hca, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hmono _ _ _ (lt_min hc hca) (min_le_right _ _) hPa
    · exact hmono _ _ _ (lt_min hc hca) (min_le_left _ _) (hcs y hy)

/-- Uniformize a "large positive constant" over a finite index set. -/
theorem uniform_large {ι : Type*} (Y : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ y K K', K ≤ K' → P y K → P y K')
    (h : ∀ y ∈ Y, ∃ K : ℝ, 0 < K ∧ P y K) : ∃ K : ℝ, 0 < K ∧ ∀ y ∈ Y, P y K := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨K, hK, hKs⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨Ka, hKa, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨max K Ka, lt_max_of_lt_left hK, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hmono _ _ _ (le_max_right _ _) hPa
    · exact hmono _ _ _ (le_max_left _ _) (hKs y hy)

/-- Second-order bound at an interior maximizer. -/
theorem taylor_max (g : ℝ → ℝ) (pl ph M : ℝ)
    (hg : DifferentiableOn ℝ g (Set.Icc pl ph))
    (hg' : DifferentiableOn ℝ (derivWithin g (Set.Icc pl ph)) (Set.Icc pl ph))
    (hM : ∀ p ∈ Set.Icc pl ph,
      |derivWithin (derivWithin g (Set.Icc pl ph)) (Set.Icc pl ph) p| ≤ M)
    (q : ℝ) (hq : q ∈ Set.Ioo pl ph) (hmax : ∀ p ∈ Set.Icc pl ph, g p ≤ g q)
    (p : ℝ) (hp : p ∈ Set.Icc pl ph) : g q - g p ≤ M * (p - q) ^ 2 := by
  set I := Set.Icc pl ph with hI
  have hqI : q ∈ I := Set.Ioo_subset_Icc_self hq
  have hInhds : I ∈ nhds q := Icc_mem_nhds hq.1 hq.2
  -- derivative vanishes at q
  have hdq : derivWithin g I q = 0 := by
    have hda : DifferentiableAt ℝ g q := (hg q hqI).differentiableAt hInhds
    have hlm : IsLocalMax g q := Filter.mem_of_superset hInhds (fun p hp => hmax p hp)
    rw [derivWithin_of_mem_nhds hInhds]
    exact hlm.deriv_eq_zero
  have hconv : Convex ℝ I := convex_Icc pl ph
  -- |g'(x)| ≤ M |x - q|
  have hg'bound : ∀ x ∈ I, |derivWithin g I x| ≤ M * |x - q| := by
    intro x hx
    have := hconv.norm_image_sub_le_of_norm_derivWithin_le hg' (fun x hx => by
      simpa [Real.norm_eq_abs] using hM x hx) hqI hx
    simpa [Real.norm_eq_abs, hdq] using this
  -- apply MVT on uIcc q p
  have hsub : Set.uIcc q p ⊆ I := hconv.ordConnected.uIcc_subset hqI hp
  have hderiv : ∀ x ∈ Set.uIcc q p,
      HasDerivWithinAt g (derivWithin g I x) (Set.uIcc q p) x := by
    intro x hx
    exact ((hg x (hsub hx)).hasDerivWithinAt).mono hsub
  have hbd : ∀ x ∈ Set.uIcc q p, ‖derivWithin g I x‖ ≤ M * |p - q| := by
    intro x hx
    rw [Real.norm_eq_abs]
    refine (hg'bound x (hsub hx)).trans ?_
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM q hqI)
    apply mul_le_mul_of_nonneg_left _ hM0
    rcases le_total q p with h | h
    · rw [Set.uIcc_of_le h] at hx
      rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith)]
      linarith [hx.2]
    · rw [Set.uIcc_of_ge h] at hx
      rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith)]
      linarith [hx.1]
  have := (convex_uIcc q p).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  have h1 : g q - g p ≤ |g p - g q| := by rw [abs_sub_comm]; exact le_abs_self _
  calc g q - g p ≤ M * |p - q| * |p - q| := h1.trans this
    _ = M * (p - q) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]


open LimitedPriceChanges.AlgorithmI in
/-- Deterministic core of Theorem B1: the plug-in gap is at most `C min(‖ẑ - z‖², r²)`. -/
theorem det_bound {E : Type*} [NormedAddCommGroup E] (pl ph : ℝ) (Y : Finset ℕ)
    (hY : Y.Nonempty) (Z : Set E) (G : ℝ → ℕ → E → ℝ) (pstar : ℕ → E → ℝ)
    (hsel : IsPriceSelection pl ph Y Z G pstar) (z : E) (hz : z ∈ Z)
    (hA : AssumptionA pl ph Y hY Z G pstar z) (ysel : E → ℕ)
    (hysel : IsLevelSelection Y Z G pstar ysel) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ zh ∈ Z,
      optValue Y hY G pstar z - G (pstar (ysel zh) zh) (ysel zh) z ≤
        C * min (‖zh - z‖ ^ 2) (r ^ 2) := by
  set opt := optValue Y hY G pstar z with hopt
  obtain ⟨c, M, hc, hM, hsd⟩ := hA.second_deriv
  -- interior radius
  obtain ⟨ρ, hρ, hρY⟩ := uniform_small Y
    (fun y ρ => ∀ p : ℝ, |p - pstar y z| < ρ → p ∈ Set.Ioo pl ph)
    (fun y c c' _ hcc' hP p hp => hP p (lt_of_lt_of_le hp hcc'))
    (fun y hy => by
      have hi := hA.interior y hy
      refine ⟨min (pstar y z - pl) (ph - pstar y z), lt_min (by linarith [hi.1])
        (by linarith [hi.2]), fun p hp => ?_⟩
      rw [abs_lt] at hp
      constructor
      · linarith [min_le_left (pstar y z - pl) (ph - pstar y z)]
      · linarith [min_le_right (pstar y z - pl) (ph - pstar y z)])
  -- Lipschitz of G at the fixed price
  obtain ⟨c₁, hc₁, hc₁Y⟩ := uniform_small Y
    (fun y c₁ => ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ z' ∈ Z, ‖z' - z‖ < c₁ →
      |G (pstar y z) y z' - G (pstar y z) y z| ≤ K₁ * ‖z' - z‖)
    (fun y c c' _ hcc' ⟨K, hK, hP⟩ => ⟨K, hK, fun z' hz' h => hP z' hz' (lt_of_lt_of_le h hcc')⟩)
    (fun y hy => by
      obtain ⟨c₁, K₁, h1, h2, h3⟩ := hA.lipschitz_G (pstar y z) (hsel y hy z hz).1 y hy
      exact ⟨c₁, h1, K₁, h2, h3⟩)
  obtain ⟨K₁, hK₁, hK₁Y⟩ := uniform_large Y
    (fun y K₁ => ∀ z' ∈ Z, ‖z' - z‖ < c₁ →
      |G (pstar y z) y z' - G (pstar y z) y z| ≤ K₁ * ‖z' - z‖)
    (fun y K K' hKK' hP z' hz' h => (hP z' hz' h).trans
      (mul_le_mul_of_nonneg_right hKK' (norm_nonneg _)))
    (fun y hy => by
      obtain ⟨K, hK, hP⟩ := hc₁Y y hy
      exact ⟨K, hK, hP⟩)
  -- Lipschitz of pstar
  obtain ⟨c₂, hc₂, hc₂Y⟩ := uniform_small Y
    (fun y c₂ => ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ z' ∈ Z, ‖z' - z‖ < c₂ →
      |pstar y z' - pstar y z| ≤ K₂ * ‖z' - z‖)
    (fun y c c' _ hcc' ⟨K, hK, hP⟩ => ⟨K, hK, fun z' hz' h => hP z' hz' (lt_of_lt_of_le h hcc')⟩)
    (fun y hy => by
      obtain ⟨c₂, K₂, h1, h2, h3⟩ := hA.lipschitz_pstar y hy
      exact ⟨c₂, h1, K₂, h2, h3⟩)
  obtain ⟨K₂, hK₂, hK₂Y⟩ := uniform_large Y
    (fun y K₂ => ∀ z' ∈ Z, ‖z' - z‖ < c₂ →
      |pstar y z' - pstar y z| ≤ K₂ * ‖z' - z‖)
    (fun y K K' hKK' hP z' hz' h => (hP z' hz' h).trans
      (mul_le_mul_of_nonneg_right hKK' (norm_nonneg _)))
    (fun y hy => by
      obtain ⟨K, hK, hP⟩ := hc₂Y y hy
      exact ⟨K, hK, hP⟩)
  -- gap
  obtain ⟨δ, hδ, hδY⟩ := uniform_small Y
    (fun y δ => G (pstar y z) y z < opt → G (pstar y z) y z < opt - δ)
    (fun y c c' _ hcc' hP h => by linarith [hP h])
    (fun y hy => hA.gap y hy)
  -- bound on the gap over all decisions
  obtain ⟨B, hB, hBY⟩ := uniform_large Y
    (fun y B => ∀ p ∈ Set.Icc pl ph, opt - G p y z ≤ B)
    (fun y B B' hBB' hP p hp => (hP p hp).trans hBB')
    (fun y hy => by
      have hcont : ContinuousOn (fun p => G p y z) (Set.Icc pl ph) :=
        ((hsd y hy z hz (by simpa using hc)).1).continuousOn
      have hne : (Set.Icc pl ph).Nonempty := ⟨pstar y z, (hsel y hy z hz).1⟩
      obtain ⟨p0, hp0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
      refine ⟨max 1 (opt - G p0 y z), lt_max_of_lt_left one_pos, fun p hp => ?_⟩
      have := hmin hp
      simp only [Set.mem_ofPred_eq] at this
      linarith [le_max_right 1 (opt - G p0 y z)])
  -- choose r
  obtain ⟨L, hL, hLpos⟩ : ∃ L : ℝ, L = K₁ + M * K₂ ^ 2 + 1 ∧ 0 < L := ⟨_, rfl, by positivity⟩
  obtain ⟨r0, hr0pos, hr0c, hr0c₁, hr0c₂, hr0ρ, hr01, hr0δ⟩ : ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ c ∧
      r0 ≤ c₁ ∧ r0 ≤ c₂ ∧ K₂ * r0 ≤ ρ ∧ r0 ≤ 1 ∧ (4 * L) * r0 ≤ δ := by
    refine ⟨min c (min c₁ (min c₂ (min (ρ / K₂) (min 1 (δ / (4 * L)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [lt_min_iff]
      exact ⟨hc, hc₁, hc₂, div_pos hρ hK₂, one_pos, div_pos hδ (by positivity)⟩
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · have : min c (min c₁ (min c₂ (min (ρ / K₂) (min 1 (δ / (4 * L)))))) ≤ ρ / K₂ :=
        (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
      rw [le_div_iff₀ hK₂] at this
      linarith
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    · have : min c (min c₁ (min c₂ (min (ρ / K₂) (min 1 (δ / (4 * L)))))) ≤ δ / (4 * L) :=
        (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
  obtain ⟨r, hr, hrpos⟩ : ∃ r : ℝ, r = r0 / 2 ∧ 0 < r := ⟨_, rfl, by positivity⟩
  have hrr0 : r < r0 := by linarith
  refine ⟨M * K₂ ^ 2 + B / r ^ 2, r, by positivity, hrpos, fun zh hzh => ?_⟩
  clear_value opt
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ‖zh - z‖ := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := hη ▸ norm_nonneg _
  rw [← hη]
  have hyh : ysel zh ∈ Y := (hysel zh hzh).1
  by_cases hclose : η < r
  · have hminη : min (η ^ 2) (r ^ 2) = η ^ 2 := min_eq_left (by nlinarith)
    rw [hminη]
    have hηc : ‖zh - z‖ < c := by rw [← hη]; linarith
    have hηc₁ : ‖zh - z‖ < c₁ := by rw [← hη]; linarith
    have hηc₂ : ‖zh - z‖ < c₂ := by rw [← hη]; linarith
    -- price perturbation bound
    have hpp : ∀ y ∈ Y, (pstar y zh - pstar y z) ^ 2 ≤ K₂ ^ 2 * η ^ 2 := by
      intro y hy
      have h1 := hK₂Y y hy zh hzh hηc₂
      rw [← hη] at h1
      calc (pstar y zh - pstar y z) ^ 2 = |pstar y zh - pstar y z| ^ 2 := (sq_abs _).symm
        _ ≤ (K₂ * η) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K₂ ^ 2 * η ^ 2 := by ring
    -- the perturbed price is interior
    have hpint : ∀ y ∈ Y, pstar y zh ∈ Set.Ioo pl ph := by
      intro y hy
      apply hρY y hy
      have h1 := hK₂Y y hy zh hzh hηc₂
      rw [← hη] at h1
      have : K₂ * η < ρ := by
        have h2 : K₂ * η < K₂ * r0 := mul_lt_mul_of_pos_left (by linarith) hK₂
        linarith
      linarith
    -- value perturbation
    have hval : ∀ y ∈ Y, |G (pstar y zh) y zh - G (pstar y z) y z| ≤
        K₁ * η + M * (K₂ ^ 2 * η ^ 2) := by
      intro y hy
      have hlip := hK₁Y y hy zh hzh hηc₁
      rw [← hη] at hlip
      rw [abs_le] at hlip ⊢
      have hlow : G (pstar y z) y zh ≤ G (pstar y zh) y zh :=
        (hsel y hy zh hzh).2 _ (hsel y hy z hz).1
      have hsd' := hsd y hy zh hzh hηc
      have htay := taylor_max (fun p => G p y zh) pl ph M hsd'.1 hsd'.2.1 hsd'.2.2
        (pstar y zh) (hpint y hy) (fun p hp => (hsel y hy zh hzh).2 p hp)
        (pstar y z) (hsel y hy z hz).1
      have h3 : M * (pstar y z - pstar y zh) ^ 2 ≤ M * (K₂ ^ 2 * η ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hM.le
        have := hpp y hy
        nlinarith
      have hMe : 0 ≤ M * (K₂ ^ 2 * η ^ 2) := by positivity
      constructor <;> linarith [hlip.1, hlip.2]
    -- the selected level is optimal at z
    obtain ⟨ys, hys, hysopt⟩ := Finset.exists_mem_eq_sup' hY (fun y => G (pstar y z) y z)
    have hopteq : opt = G (pstar ys z) ys z := by rw [hopt]; exact hysopt
    have hsmall : 2 * (K₁ * η + M * (K₂ ^ 2 * η ^ 2)) < δ := by
      have hηr0 : η < r0 := by linarith
      have hη1 : η ≤ 1 := by linarith
      have hη2 : η ^ 2 ≤ η := by nlinarith
      have h5 : 2 * (K₁ * η + M * (K₂ ^ 2 * η ^ 2)) ≤ 2 * L * η := by
        have : M * (K₂ ^ 2 * η ^ 2) ≤ M * K₂ ^ 2 * η := by
          have := mul_le_mul_of_nonneg_left hη2 (by positivity : (0:ℝ) ≤ M * K₂ ^ 2)
          linarith
        have hLη : L * η = K₁ * η + M * K₂ ^ 2 * η + η := by rw [hL]; ring
        linarith
      have h6 : 2 * L * η < 4 * L * r0 := by
        have : L * η < L * r0 := mul_lt_mul_of_pos_left hηr0 hLpos
        have : 0 < L * r0 := by positivity
        linarith
      linarith
    have hyopt : G (pstar (ysel zh) z) (ysel zh) z = opt := by
      have hle : G (pstar (ysel zh) z) (ysel zh) z ≤ opt := by
        rw [hopt]; exact Finset.le_sup' (fun y => G (pstar y z) y z) hyh
      have hv1 := abs_le.mp (hval _ hyh)
      have hv2 := abs_le.mp (hval _ hys)
      have hsl := (hysel zh hzh).2 ys hys
      by_contra hne
      have hlt := hδY _ hyh (lt_of_le_of_ne hle hne)
      linarith
    -- final Taylor bound at z
    have hsdz := hsd _ hyh z hz (by simpa using hc)
    have htay := taylor_max (fun p => G p (ysel zh) z) pl ph M hsdz.1 hsdz.2.1 hsdz.2.2
      (pstar (ysel zh) z) (hA.interior _ hyh) (fun p hp => (hsel _ hyh z hz).2 p hp)
      (pstar (ysel zh) zh) (hsel _ hyh zh hzh).1
    have h3 : M * (pstar (ysel zh) zh - pstar (ysel zh) z) ^ 2 ≤ M * (K₂ ^ 2 * η ^ 2) :=
      mul_le_mul_of_nonneg_left (hpp _ hyh) hM.le
    have hBr : 0 ≤ B / r ^ 2 * η ^ 2 := by positivity
    have hexp : (M * K₂ ^ 2 + B / r ^ 2) * η ^ 2 = M * (K₂ ^ 2 * η ^ 2) + B / r ^ 2 * η ^ 2 := by
      ring
    rw [hexp]
    linarith
  · push Not at hclose
    have hminr : min (η ^ 2) (r ^ 2) = r ^ 2 := min_eq_right (by nlinarith)
    rw [hminr]
    have h1 := hBY _ hyh _ (hsel _ hyh zh hzh).1
    have h2 : (M * K₂ ^ 2 + B / r ^ 2) * r ^ 2 = M * K₂ ^ 2 * r ^ 2 + B := by
      field_simp
    rw [h2]
    have : 0 ≤ M * K₂ ^ 2 * r ^ 2 := by positivity
    linarith

end LPCB1Aux

namespace LPCB1Aux

/-- Discretized layer-cake bound. -/
theorem grid_bound (n : ℕ) (hn : 1 ≤ n) (r η : ℝ) (hη : 0 ≤ η) :
    min (η ^ 2) (r ^ 2) ≤ 1 / (n : ℝ) + ∑ k ∈ Finset.Icc 1 ⌈(n : ℝ) * r ^ 2⌉₊,
      (1 / (n : ℝ)) * (if Real.sqrt ((k : ℝ) / n) ≤ η then 1 else 0) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set x := min (η ^ 2) (r ^ 2) with hx
  by_cases hx0 : x < 0
  · have : 0 ≤ 1 / (n : ℝ) + ∑ k ∈ Finset.Icc 1 ⌈(n : ℝ) * r ^ 2⌉₊,
      (1 / (n : ℝ)) * (if Real.sqrt ((k : ℝ) / n) ≤ η then 1 else 0) := by
      apply add_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro k _
      split_ifs <;> positivity
    linarith
  push Not at hx0
  set j := ⌊(n : ℝ) * x⌋₊ with hj
  have hxη : x ≤ η ^ 2 := min_le_left _ _
  have hxr : x ≤ r ^ 2 := min_le_right _ _
  have hjN : j ≤ ⌈(n : ℝ) * r ^ 2⌉₊ := by
    apply Nat.floor_le_ceil _ |>.trans
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hxr hnpos.le)
  have hsub : Finset.Icc 1 j ⊆ Finset.Icc 1 ⌈(n : ℝ) * r ^ 2⌉₊ :=
    Finset.Icc_subset_Icc le_rfl hjN
  have hterm : ∀ k ∈ Finset.Icc 1 j,
      (1 / (n : ℝ)) * (if Real.sqrt ((k : ℝ) / n) ≤ η then 1 else 0) = 1 / (n : ℝ) := by
    intro k hk
    have hkj : (k : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hjx : (j : ℝ) ≤ n * x := Nat.floor_le (by positivity)
    have hkx : (k : ℝ) / n ≤ η ^ 2 := by
      rw [div_le_iff₀ hnpos]; nlinarith
    have : Real.sqrt ((k : ℝ) / n) ≤ η := by
      exact Real.sqrt_le_iff.mpr ⟨hη, hkx⟩
    rw [if_pos this, mul_one]
  have hsum1 : ∑ k ∈ Finset.Icc 1 j,
      (1 / (n : ℝ)) * (if Real.sqrt ((k : ℝ) / n) ≤ η then 1 else 0) = j / n := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp [div_eq_mul_inv]
  have hsum2 : ∑ k ∈ Finset.Icc 1 j,
      (1 / (n : ℝ)) * (if Real.sqrt ((k : ℝ) / n) ≤ η then 1 else 0) ≤
      ∑ k ∈ Finset.Icc 1 ⌈(n : ℝ) * r ^ 2⌉₊,
      (1 / (n : ℝ)) * (if Real.sqrt ((k : ℝ) / n) ≤ η then 1 else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _
    split_ifs <;> positivity
  have hxj : (n : ℝ) * x < j + 1 := Nat.lt_floor_add_one _
  have hx' : x ≤ 1 / n + j / n := by
    rw [← add_div, le_div_iff₀ hnpos]; linarith
  linarith

end LPCB1Aux

namespace LPCB1Aux

/-- Real arithmetic: the grid sum is `O(1/n)`. -/
theorem real_sum_bound (n : ℕ) (hn : 1 ≤ n) (C r K₁₄ K₁₅ K₁₆ : ℝ) (hC : 0 < C)
    (hK₁₄ : 0 < K₁₄) (hK₁₅ : 0 < K₁₅) (hK₁₆ : 0 < K₁₆) :
    C / n + ∑ k ∈ Finset.Icc 1 ⌈(n : ℝ) * r ^ 2⌉₊,
      C / n * (K₁₄ * Real.exp (-((n : ℝ) * K₁₅ * Real.sqrt ((k : ℝ) / n) ^ 2)) + K₁₆ / n) ≤
    C * (1 + K₁₄ / (1 - Real.exp (-K₁₅)) + (r ^ 2 + 1) * K₁₆) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set q := Real.exp (-K₁₅) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set N := ⌈(n : ℝ) * r ^ 2⌉₊ with hN
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      C / n * (K₁₄ * Real.exp (-((n : ℝ) * K₁₅ * Real.sqrt ((k : ℝ) / n) ^ 2)) + K₁₆ / n) =
      C / n * K₁₄ * q ^ k + C / n * (K₁₆ / n) := by
    intro k _
    rw [Real.sq_sqrt (by positivity)]
    have : -((n : ℝ) * K₁₅ * ((k : ℝ) / n)) = (k : ℕ) * (-K₁₅) := by
      field_simp
    rw [this, Real.exp_nat_mul]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hgeom : ∑ k ∈ Finset.Icc 1 N, q ^ k ≤ 1 / (1 - q) := by
    have h1 : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
    rw [h1]
    refine (geom_sum_Ico_le_of_lt_one hq0 hq1).trans ?_
    apply div_le_div_of_nonneg_right _ (by linarith)
    simpa using hq1.le
  have hNle : ((N + 1 - 1 : ℕ) : ℝ) ≤ n * (r ^ 2 + 1) := by
    have : N + 1 - 1 = N := by omega
    rw [this]
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ n * r ^ 2)
    nlinarith
  have hA : C / n * K₁₄ * ∑ k ∈ Finset.Icc 1 N, q ^ k ≤ C / n * K₁₄ * (1 / (1 - q)) :=
    mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hB : ((N + 1 - 1 : ℕ) : ℝ) * (C / n * (K₁₆ / n)) ≤ C / n * ((r ^ 2 + 1) * K₁₆) := by
    have : ((N + 1 - 1 : ℕ) : ℝ) * (C / n * (K₁₆ / n)) =
        (C / n) * (K₁₆ / n * ((N + 1 - 1 : ℕ) : ℝ)) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
    nlinarith
  have hfin : C * (1 + K₁₄ / (1 - q) + (r ^ 2 + 1) * K₁₆) / n =
      C / n + C / n * K₁₄ * (1 / (1 - q)) + C / n * ((r ^ 2 + 1) * K₁₆) := by
    field_simp
  rw [hfin]
  linarith

end LPCB1Aux

namespace LPCThm1Aux

/-- The law of an adapted price process has total mass one. -/
theorem mass_eq_one (f : ℕ → ℝ → ℝ) (Pset : Set ℝ) (hf0 : ∀ p ∈ Pset, ∀ d, 0 ≤ f d p)
    (hf1 : ∀ p ∈ Pset, HasSum (fun d => f d p) 1) :
    ∀ (T : ℕ) (price : Fin T → (Fin T → ℕ) → ℝ), (∀ s d, price s d ∈ Pset) →
      (∀ s d d', (∀ t : Fin T, t < s → d t = d' t) → price s d = price s d') →
      ∑' d : Fin T → ℕ, ∏ s, ENNReal.ofReal (f (d s) (price s d)) = 1 := by
  intro T
  induction T with
  | zero =>
    intro price _ _
    rw [tsum_eq_single (fun i => i.elim0)]
    · simp
    · intro d hd
      exact absurd (funext (fun i => i.elim0)) hd
  | succ T ih =>
    intro price hP hadapt
    let price' : Fin T → (Fin T → ℕ) → ℝ := fun s g => price (Fin.castSucc s) (Fin.snoc g 0)
    let q : (Fin T → ℕ) → ℝ := fun g => price (Fin.last T) (Fin.snoc g 0)
    have hsnoc : ∀ (g : Fin T → ℕ) (a : ℕ),
        ∏ s : Fin (T + 1), ENNReal.ofReal (f ((Fin.snoc g a : Fin (T + 1) → ℕ) s)
          (price s (Fin.snoc g a))) =
        (∏ s : Fin T, ENNReal.ofReal (f (g s) (price' s g))) * ENNReal.ofReal (f a (q g)) := by
      intro g a
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro s _
        simp only [Fin.snoc_castSucc, price']
        congr 2
        apply hadapt
        intro t ht
        have : (t : ℕ) < T := by
          have := s.isLt
          have h2 : (t : ℕ) < (s : ℕ) := by simpa [Fin.lt_def] using ht
          omega
        have ht' : t = Fin.castSucc ⟨t, this⟩ := by ext; simp
        rw [ht', Fin.snoc_castSucc, Fin.snoc_castSucc]
      · simp only [Fin.snoc_last, q]
        congr 2
        apply hadapt
        intro t ht
        have : (t : ℕ) < T := by simpa [Fin.lt_def] using ht
        have ht' : t = Fin.castSucc ⟨t, this⟩ := by ext; simp
        rw [ht', Fin.snoc_castSucc, Fin.snoc_castSucc]
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    have hrw : ∀ (g : Fin T → ℕ) (a : ℕ),
        (∏ s : Fin (T + 1), ENNReal.ofReal (f ((Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ) (a, g)) s)
          (price s (Fin.snocEquiv (fun _ : Fin (T + 1) => ℕ) (a, g))))) =
        (∏ s : Fin T, ENNReal.ofReal (f (g s) (price' s g))) * ENNReal.ofReal (f a (q g)) :=
      fun g a => hsnoc g a
    simp_rw [hrw, ENNReal.tsum_mul_left]
    have hone : ∀ g : Fin T → ℕ, ∑' a : ℕ, ENNReal.ofReal (f a (q g)) = 1 := by
      intro g
      have hq : q g ∈ Pset := hP _ _
      rw [← ENNReal.ofReal_tsum_of_nonneg (hf0 _ hq) (hf1 _ hq).summable, (hf1 _ hq).tsum_eq,
        ENNReal.ofReal_one]
    simp_rw [hone, mul_one]
    apply ih price' (fun s g => hP _ _)
    intro s g g' hgg
    simp only [price']
    apply hadapt
    intro t ht
    by_cases htT : (t : ℕ) < T
    · have ht' : t = Fin.castSucc ⟨t, htT⟩ := by ext; simp
      rw [ht', Fin.snoc_castSucc, Fin.snoc_castSucc]
      apply hgg
      simpa [Fin.lt_def] using ht
    · exfalso
      have := s.isLt
      simp [Fin.lt_def] at ht
      omega


open LimitedPriceChanges.AlgorithmI

theorem runStage_congr (d d' : ℕ → ℕ) (ytil : ℕ) : ∀ n s0 x,
    (∀ t, s0 ≤ t → t < s0 + n → d t = d' t) →
    Alg.runStage d ytil s0 n x = Alg.runStage d' ytil s0 n x := by
  intro n
  induction n with
  | zero => intro s0 x _; simp [Alg.runStage]
  | succ n ih =>
    intro s0 x h
    simp only [Alg.runStage]
    have h0 : d s0 = d' s0 := h s0 le_rfl (by omega)
    rw [h0, ih (s0 + 1) _ (fun t ht1 ht2 => h t (by omega) (by omega))]

theorem runStage_le (d : ℕ → ℕ) (ytil B : ℕ) (hy : ytil ≤ B) : ∀ n s0 x, x ≤ B →
    (Alg.runStage d ytil s0 n x).2 ≤ B := by
  intro n
  induction n with
  | zero => intro s0 x hx; simpa [Alg.runStage] using hx
  | succ n ih =>
    intro s0 x hx
    simp only [Alg.runStage]
    apply ih
    have : max x ytil ≤ B := max_le hx hy
    omega

variable {S : Model} (A : Alg S)

theorem stageStart_mono (T : ℕ) {a b : ℕ} (hab : a ≤ b) : A.stageStart T a ≤ A.stageStart T b := by
  unfold Alg.stageStart
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hab)

theorem stageStart_succ (T i : ℕ) (hi : 1 ≤ i) :
    A.stageStart T (i + 1) = A.stageStart T i + A.stageLen T i := by
  unfold Alg.stageStart
  rw [Finset.sum_Ico_succ_top hi]

theorem stageState_congr (T : ℕ) : ∀ k (d d' : ℕ → ℕ),
    (∀ t, t < A.stageStart T (k + 1) → d t = d' t) →
    A.stageState T d k = A.stageState T d' k := by
  intro k
  induction k with
  | zero => intro d d' _; simp [Alg.stageState]
  | succ k ih =>
    intro d d' h
    have hk := ih d d' (fun t ht => h t (lt_of_lt_of_le ht (stageStart_mono A T (by omega))))
    simp only [Alg.stageState]
    rw [hk]
    have hsucc := stageStart_succ A T (k + 1) (by omega)
    rw [runStage_congr d d' _ (A.stageLen T (k + 1)) (A.stageStart T (k + 1)) _
      (fun t _ ht2 => h t (by omega))]

theorem stageOf_le (T s : ℕ) : A.stageOf T s ≤ A.m + 1 := by
  unfold Alg.stageOf
  have := Finset.card_filter_le (Finset.Icc 1 A.m) (fun j => A.stageStart T (j + 1) ≤ s)
  simp at this
  omega

theorem one_le_stageOf (T s : ℕ) : 1 ≤ A.stageOf T s := by
  unfold Alg.stageOf; omega

theorem stageStart_stageOf_le (T s : ℕ) : A.stageStart T (A.stageOf T s) ≤ s := by
  set i := A.stageOf T s with hi
  by_cases hi1 : i = 1
  · rw [hi1]; simp [Alg.stageStart]
  have hi2 : 2 ≤ i := by have := one_le_stageOf A T s; omega
  set F := (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ s) with hF
  have hcard : F.card = i - 1 := by
    rw [hi]; unfold Alg.stageOf; rw [← hF]; omega
  by_contra hlt
  push Not at hlt
  have hsub : F ⊆ Finset.Icc 1 (i - 2) := by
    intro j hj
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_Icc]
    refine ⟨hj.1.1, ?_⟩
    by_contra hji
    have : A.stageStart T i ≤ A.stageStart T (j + 1) := stageStart_mono A T (by omega)
    omega
  have := Finset.card_le_card hsub
  simp at this
  omega

theorem price_adapted (T : ℕ) (s : Fin T) (d d' : Fin T → ℕ)
    (h : ∀ t : Fin T, t < s → d t = d' t) : A.price T s d = A.price T s d' := by
  unfold Alg.price Alg.phat
  congr 1
  apply stageState_congr
  intro t ht
  have h1 : A.stageOf T s - 1 + 1 = A.stageOf T s := by
    have := one_le_stageOf A T s; omega
  rw [h1] at ht
  have hts : t < s := lt_of_lt_of_le ht (stageStart_stageOf_le A T s)
  have htT : t < T := lt_trans hts s.isLt
  simp only [Alg.extend, dif_pos htT]
  exact h ⟨t, htT⟩ (by simpa [Fin.lt_def] using hts)

theorem ytildeOf_mem (y : ℕ) (hy : y ∈ S.Y) : A.ytildeOf y ∈ S.Y := by
  unfold Alg.ytildeOf
  simp only [Model.Y, Finset.mem_Icc] at hy ⊢
  split_ifs
  · exact hy
  · constructor
    · exact le_min (le_max_right _ _) S.yl_le_yh
    · exact min_le_right _ _

theorem stageState_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ)
    (d : ℕ → ℕ) : ∀ k, (A.stageState T d k).1 ∈ S.P ∧ (A.stageState T d k).2.1 ∈ S.Y ∧
      (A.stageState T d k).2.2 ≤ S.yh := by
  intro k
  induction k with
  | zero => exact ⟨hA.p1_mem, hA.y1_mem, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨hp, hy, hx⟩ := ih
    simp only [Alg.stageState]
    set r := Alg.runStage d (A.ytildeOf (A.stageState T d k).2.1) (A.stageStart T (k + 1))
      (A.stageLen T (k + 1)) (A.stageState T d k).2.2
    have hz : A.mle (A.stageState T d k).1 r.1 ∈ S.Z := (hA.mle _ hp r.1).1
    have hyk : A.yplug (A.mle (A.stageState T d k).1 r.1) ∈ S.Y := (hA.plugIn _ hz).1
    refine ⟨(hS.priceSelection _ hyk _ hz).1, hyk, ?_⟩
    have hyt := ytildeOf_mem A _ hy
    simp only [Model.Y, Finset.mem_Icc] at hyt
    exact runStage_le d _ S.yh hyt.2 _ _ _ hx

theorem price_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ) (s : Fin T)
    (d : Fin T → ℕ) : A.price T s d ∈ S.P :=
  (stageState_mem A z hS hA T _ _).1

theorem phat_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T i : ℕ)
    (d : Fin T → ℕ) : A.phat T i d ∈ S.P :=
  (stageState_mem A z hS hA T _ _).1

theorem yhat_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T i : ℕ)
    (d : Fin T → ℕ) : A.yhat T i d ∈ S.Y :=
  (stageState_mem A z hS hA T _ _).2.1

theorem level_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ) (s : Fin T)
    (d : Fin T → ℕ) : A.level T s d ∈ S.Y := by
  unfold Alg.level
  have hyt := ytildeOf_mem A _ (yhat_mem A z hS hA T (A.stageOf T s) d)
  have hx := (stageState_mem A z hS hA T (Alg.extend d) (A.stageOf T s - 1)).2.2
  simp only [Model.Y, Finset.mem_Icc] at hyt ⊢
  have hr := runStage_le (Alg.extend d) (A.ytilde T (A.stageOf T s) d) S.yh hyt.2
    ((s : ℕ) - A.stageStart T (A.stageOf T s)) (A.stageStart T (A.stageOf T s)) _ hx
  exact ⟨le_trans hyt.1 (le_max_right _ _), max_le hr hyt.2⟩

theorem mass_one (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T : ℕ) :
    ∑' d : Fin T → ℕ, A.pathWeight z T d = 1 := by
  unfold Alg.pathWeight
  exact mass_eq_one (fun d p => S.f d p z) S.P
    (fun p hp d => S.f_nonneg p hp z hS.z_mem d) (fun p hp => S.f_hasSum p hp z hS.z_mem)
    T (fun s d => A.price T s d) (fun s d => price_mem A z hS hA T s d)
    (fun s d d' h => price_adapted A T s d d' h)

end LPCThm1Aux

namespace LPCThm1Aux

open LimitedPriceChanges.AlgorithmI

theorem uniform_large {ι : Type*} (Y : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ y K K', K ≤ K' → P y K → P y K')
    (h : ∀ y ∈ Y, ∃ K : ℝ, 0 < K ∧ P y K) : ∃ K : ℝ, 0 < K ∧ ∀ y ∈ Y, P y K := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨K, hK, hKs⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨Ka, hKa, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨max K Ka, lt_max_of_lt_left hK, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hmono _ _ _ (le_max_right _ _) hPa
    · exact hmono _ _ _ (le_max_left _ _) (hKs y hy)

theorem G_le_Gstar (S : Model) (pstar : ℕ → ℝ → ℝ) (z : ℝ) (hz : z ∈ S.Z)
    (hsel : S.IsPriceSelection pstar) (p : ℝ) (hp : p ∈ S.P) (y : ℕ) (hy : y ∈ S.Y) :
    S.G p y z ≤ S.Gstar pstar z := by
  have h1 := (hsel y hy z hz).2 p hp
  have h2 : S.G (pstar y z) y z ≤ S.Gstar pstar z :=
    Finset.le_sup' (fun y => S.G (pstar y z) y z) hy
  linarith

theorem gap_bound (S : Model) (pstar : ℕ → ℝ → ℝ) (z : ℝ) (hS : S.Standing pstar z) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S.P, ∀ y ∈ S.Y, S.Gstar pstar z - S.G p y z ≤ B := by
  obtain ⟨c, M, hc, hM, hsd⟩ := hS.assumptionA.second_deriv
  have key : ∀ y ∈ S.Y, ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S.P, S.Gstar pstar z - S.G p y z ≤ B := by
    intro y hy
    have hcont : ContinuousOn (fun p => S.G p y z) (Set.Icc S.pl S.ph) :=
      ((hsd y hy z hS.z_mem (by simpa using hc)).1).continuousOn
    have hne : (Set.Icc S.pl S.ph).Nonempty := ⟨S.pl, Set.left_mem_Icc.mpr S.pl_le_ph⟩
    obtain ⟨p0, hp0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
    refine ⟨max 1 (S.Gstar pstar z - S.G p0 y z), lt_max_of_lt_left one_pos, fun p hp => ?_⟩
    have := hmin hp
    simp only [Set.mem_ofPred_eq] at this
    linarith [le_max_right 1 (S.Gstar pstar z - S.G p0 y z)]
  obtain ⟨B, hB, hBY⟩ := uniform_large S.Y
    (fun y B => ∀ p ∈ S.P, S.Gstar pstar z - S.G p y z ≤ B)
    (fun y B B' hBB' hP p hp => (hP p hp).trans hBB') key
  exact ⟨B, hB, fun p hp y hy => hBY y hy p hp⟩

end LPCThm1Aux

namespace LPCThm1Aux

open LimitedPriceChanges.AlgorithmI

theorem pointwise (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid)
    (B : ℝ) (hBb : ∀ p ∈ S.P, ∀ y ∈ S.Y, S.Gstar A.pstar z - S.G p y z ≤ B)
    (T : ℕ) (s : Fin T) (d : Fin T → ℕ) :
    ENNReal.ofReal (S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z) ≤
      (if A.stageOf T s = 1 then ENNReal.ofReal B else 0) +
      (if 2 ≤ A.stageOf T s then
          ENNReal.ofReal (S.Gstar A.pstar z -
            S.G (A.phat T (A.stageOf T s) d) (A.yhat T (A.stageOf T s) d) z)
        else 0) +
      (if 2 ≤ A.stageOf T s then
          (if A.yhat T (A.stageOf T s) d ≠ A.ytilde T (A.stageOf T s) d then ENNReal.ofReal B
            else 0)
        else 0) +
      ∑ j ∈ Finset.Icc 2 (A.m + 1), ENNReal.ofReal B *
        (if A.stageOf T s = j ∧ A.level T s d ≠ A.ytilde T j d then (1 : ENNReal) else 0) := by
  have hp := price_mem A z hS hA T s d
  have hl := level_mem A z hS hA T s d
  have hg : S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z ≤ B := hBb _ hp _ hl
  by_cases h1 : A.stageOf T s = 1
  · rw [if_pos h1]
    exact le_add_right (le_add_right (le_add_right (ENNReal.ofReal_le_ofReal hg)))
  · have h2 : 2 ≤ A.stageOf T s := by have := one_le_stageOf A T s; omega
    rw [if_neg h1, if_pos h2, if_pos h2, zero_add]
    set i := A.stageOf T s with hi
    have hpe : A.price T s d = A.phat T i d := rfl
    have hph := phat_mem A z hS hA T i d
    have hyh := yhat_mem A z hS hA T i d
    have hGle := G_le_Gstar S A.pstar z hS.z_mem hS.priceSelection _ hph _ hyh
    have hsplit : S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z =
        (S.Gstar A.pstar z - S.G (A.phat T i d) (A.yhat T i d) z) +
        (S.G (A.phat T i d) (A.yhat T i d) z - S.G (A.price T s d) (A.level T s d) z) := by ring
    rw [hsplit]
    refine (ENNReal.ofReal_add_le).trans ?_
    rw [add_assoc]
    gcongr
    by_cases hlv : A.level T s d = A.yhat T i d
    · rw [hlv, hpe, sub_self, ENNReal.ofReal_zero]; exact zero_le
    · have hb : ENNReal.ofReal (S.G (A.phat T i d) (A.yhat T i d) z -
          S.G (A.price T s d) (A.level T s d) z) ≤ ENNReal.ofReal B :=
        ENNReal.ofReal_le_ofReal (by linarith)
      by_cases hyt : A.yhat T i d ≠ A.ytilde T i d
      · rw [if_pos hyt]; exact le_add_right hb
      · push Not at hyt
        rw [if_neg (not_not.mpr hyt), zero_add]
        have hmem : i ∈ Finset.Icc 2 (A.m + 1) :=
          Finset.mem_Icc.mpr ⟨h2, stageOf_le A T s⟩
        have hterm : ENNReal.ofReal B *
            (if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0) =
            ENNReal.ofReal B := by
          rw [if_pos ⟨rfl, by rw [← hyt]; exact hlv⟩, mul_one]
        refine hb.trans (hterm.symm.le.trans ?_)
        exact Finset.single_le_sum (f := fun j => ENNReal.ofReal B *
          (if A.stageOf T s = j ∧ A.level T s d ≠ A.ytilde T j d then (1 : ENNReal) else 0))
          (fun j _ => zero_le) hmem

end LPCThm1Aux

namespace LPC25Aux

open LimitedPriceChanges.AlgorithmI

variable {S : Model} (A : Alg S)

theorem stageStart_mono (T : ℕ) {a b : ℕ} (hab : a ≤ b) : A.stageStart T a ≤ A.stageStart T b := by
  unfold Alg.stageStart
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hab)

theorem stageStart_succ (T i : ℕ) (hi : 1 ≤ i) :
    A.stageStart T (i + 1) = A.stageStart T i + A.stageLen T i := by
  unfold Alg.stageStart
  rw [Finset.sum_Ico_succ_top hi]

theorem stageOf_le (T s : ℕ) : A.stageOf T s ≤ A.m + 1 := by
  unfold Alg.stageOf
  have := Finset.card_filter_le (Finset.Icc 1 A.m) (fun j => A.stageStart T (j + 1) ≤ s)
  simp at this
  omega

theorem one_le_stageOf (T s : ℕ) : 1 ≤ A.stageOf T s := by
  unfold Alg.stageOf; omega

/-- A period of stage `i ≥ 2` lies in `[tᵢ, tᵢ + Iᵢ)`, provided `t_{m+1} ≤ T` and `s < T`. -/
theorem mem_stage (T s i : ℕ) (hs : s < T) (hT : A.stageStart T (A.m + 1) ≤ T)
    (hi2 : 2 ≤ i) (hsi : A.stageOf T s = i) :
    A.stageStart T i ≤ s ∧ s < A.stageStart T i + A.stageLen T i := by
  have him : i ≤ A.m + 1 := hsi ▸ stageOf_le A T s
  set F := (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ s) with hF
  have hcard : F.card = i - 1 := by
    unfold Alg.stageOf at hsi; rw [← hF] at hsi; omega
  constructor
  · by_contra hlt
    push Not at hlt
    have hsub : F ⊆ Finset.Icc 1 (i - 2) := by
      intro j hj
      rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]
      refine ⟨hj.1.1, ?_⟩
      by_contra hji
      have : A.stageStart T i ≤ A.stageStart T (j + 1) := stageStart_mono A T (by omega)
      omega
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_cases hile : i ≤ A.m
    · rw [← stageStart_succ A T i (by omega)]
      by_contra hge
      push Not at hge
      have hsub : Finset.Icc 1 i ⊆ F := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [hF, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hj.1, by omega⟩, ?_⟩
        exact (stageStart_mono A T (by omega)).trans hge
      have := Finset.card_le_card hsub
      simp at this
      omega
    · have hieq : i = A.m + 1 := by omega
      subst hieq
      have hlen : A.stageLen T (A.m + 1) = T - ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
        unfold Alg.stageLen; simp
      have hstart : A.stageStart T (A.m + 1) = ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
        unfold Alg.stageStart
        apply Finset.sum_congr (by ext j; simp [Finset.mem_Ico, Finset.mem_Icc])
        intro j hj
        simp [Finset.mem_Icc] at hj
        unfold Alg.stageLen
        rw [if_pos hj.2]
      rw [hlen]
      rw [hstart] at hT ⊢
      omega

/-- The number of periods of stage `i ≥ 2` is at most `Iᵢ`. -/
theorem card_stage (T i : ℕ) (hT : A.stageStart T (A.m + 1) ≤ T) (hi2 : 2 ≤ i) :
    ((Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card ≤
      A.stageLen T i := by
  have := Finset.card_le_card_of_injOn (fun s : Fin T => (s : ℕ))
    (s := (Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = i))
    (t := Finset.Ico (A.stageStart T i) (A.stageStart T i + A.stageLen T i))
    (fun s hs => by
      have hs' : A.stageOf T (s : ℕ) = i := by simpa using hs
      have := mem_stage A T s i s.isLt hT hi2 hs'
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact this)
    (fun a _ b _ h => Fin.ext h)
  simpa using this


theorem stageStart_last (T : ℕ) :
    A.stageStart T (A.m + 1) = ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j := by
  unfold Alg.stageStart
  apply Finset.sum_congr (by ext j; simp [Finset.mem_Ico, Finset.mem_Icc])
  intro j hj
  simp [Finset.mem_Icc] at hj
  unfold Alg.stageLen
  rw [if_pos hj.2]

/-- `T^{j/(m+1)} = u^j` with `u = T^{1/(m+1)}`. -/
theorem rpow_eq_pow (T : ℕ) (m j : ℕ) :
    (T : ℝ) ^ ((j : ℝ) / ((m : ℝ) + 1)) = ((T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem u_pow_succ (T m : ℕ) :
    ((T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ (m + 1) = T := by
  rw [← rpow_eq_pow]
  have : ((m + 1 : ℕ) : ℝ) / ((m : ℝ) + 1) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]

theorem u_ge (T m : ℕ) (hT : (2 * m) ^ (m + 1) ≤ T) :
    (2 * m : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  have h1 : ((2 * m : ℝ) ^ (m + 1)) ^ ((((m + 1 : ℕ) : ℝ))⁻¹) = 2 * m :=
    Real.pow_rpow_inv_natCast (by positivity) (by omega)
  have h2 : ((m + 1 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / ((m : ℝ) + 1) := by push_cast; ring
  rw [h2] at h1
  rw [← h1]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast hT

/-- For `u ≥ 2m`, the first `m` stages fit in the horizon. -/
theorem stages_fit (T : ℕ) (hm : 1 ≤ A.m) (hT : (2 * A.m) ^ (A.m + 1) ≤ T) :
    A.stageStart T (A.m + 1) ≤ T := by
  rw [stageStart_last]
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu2 : (2 * A.m : ℝ) ≤ u := u_ge T A.m hT
  have hm1 : (1 : ℝ) ≤ A.m := by exact_mod_cast hm
  have hu1 : 1 ≤ u := by linarith
  have hsum : (∑ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ)) ≤ A.m * (u ^ A.m + 1) := by
    have : ∀ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ) ≤ u ^ A.m + 1 := by
      intro j hj
      have hj := Finset.mem_Icc.mp hj
      unfold Alg.ceilLen
      rw [rpow_eq_pow, ← hu]
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u ^ j)
      have h2 : u ^ j ≤ u ^ A.m := pow_le_pow_right₀ hu1 hj.2
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    simp; ring_nf; exact le_refl _
  have hpow : (1 : ℝ) ≤ u ^ A.m := one_le_pow₀ hu1
  have hT' : (T : ℝ) = u * u ^ A.m := by rw [hu, ← pow_succ', u_pow_succ]
  have : (∑ j ∈ Finset.Icc 1 A.m, (A.ceilLen T j : ℝ)) ≤ T := by
    rw [hT']
    refine hsum.trans ?_
    nlinarith
  exact_mod_cast this

/-- `Iᵢ ≤ 2 T^{1/(m+1)} Iᵢ₋₁` and `Iᵢ₋₁ > 0` for `2 ≤ i ≤ m + 1`. -/
theorem ratio (T : ℕ) (hT1 : 1 ≤ T) (i : ℕ) (hi : i ∈ Finset.Icc 2 (A.m + 1)) :
    0 < (A.stageLen T (i - 1) : ℝ) ∧
    (A.stageLen T i : ℝ) ≤ 2 * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) * A.stageLen T (i - 1) := by
  have hi := Finset.mem_Icc.mp hi
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
  have hprev : u ^ (i - 1) ≤ (A.stageLen T (i - 1) : ℝ) := by
    unfold Alg.stageLen
    rw [if_pos (by omega)]
    unfold Alg.ceilLen
    rw [rpow_eq_pow, ← hu]
    exact Nat.le_ceil _
  have hpos : 0 < u ^ (i - 1) := by positivity
  refine ⟨lt_of_lt_of_le hpos hprev, ?_⟩
  have hcur : (A.stageLen T i : ℝ) ≤ 2 * u ^ i := by
    by_cases him : i ≤ A.m
    · unfold Alg.stageLen
      rw [if_pos him]
      unfold Alg.ceilLen
      rw [rpow_eq_pow, ← hu]
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u ^ i)
      have h2 : 1 ≤ u ^ i := one_le_pow₀ hu1
      linarith
    · have hieq : i = A.m + 1 := by omega
      have h1 : A.stageLen T i ≤ T := by
        unfold Alg.stageLen; rw [if_neg him]; omega
      have h2 : (T : ℝ) = u ^ i := by rw [hieq, hu, u_pow_succ]
      have h3 : (A.stageLen T i : ℝ) ≤ T := by exact_mod_cast h1
      have h4 : 0 ≤ u ^ i := by positivity
      linarith
  have hui : u ^ i = u * u ^ (i - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc (A.stageLen T i : ℝ) ≤ 2 * u ^ i := hcur
    _ = 2 * u * u ^ (i - 1) := by rw [hui]; ring
    _ ≤ 2 * u * A.stageLen T (i - 1) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)

theorem expect_sum (z : ℝ) (T : ℕ) (F : Fin T → (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => ∑ s : Fin T, F s d) = ∑ s : Fin T, A.expect z T (F s) := by
  unfold Alg.expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

end LPC25Aux

namespace LPC25Aux

open LimitedPriceChanges.AlgorithmI

variable {S : Model} (A : Alg S)

/-- `∑_{s : stage ≥ 2} c / I_{stage(s) - 1} ≤ 2 c m T^{1/(m+1)}`. -/
theorem stage_sum_bound (T : ℕ) (hT1 : 1 ≤ T) (hfit : A.stageStart T (A.m + 1) ≤ T)
    (c : ℝ) (hc : 0 ≤ c) :
    ∑ s : Fin T, (if 2 ≤ A.stageOf T s then c / (A.stageLen T (A.stageOf T s - 1) : ℝ) else 0) ≤
      2 * c * A.m * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) := by
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hregroup : ∀ s : Fin T,
      (if 2 ≤ A.stageOf T s then c / (A.stageLen T (A.stageOf T s - 1) : ℝ) else 0) =
      ∑ i ∈ Finset.Icc 2 (A.m + 1),
        (if A.stageOf T s = i then c / (A.stageLen T (i - 1) : ℝ) else 0) := by
    intro s
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Icc]
    have := stageOf_le A T s
    by_cases h2 : 2 ≤ A.stageOf T s
    · rw [if_pos h2, if_pos ⟨h2, this⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.1)]
  rw [Finset.sum_congr rfl (fun s _ => hregroup s), Finset.sum_comm]
  have hstage : ∀ i ∈ Finset.Icc 2 (A.m + 1),
      ∑ s : Fin T, (if A.stageOf T s = i then c / (A.stageLen T (i - 1) : ℝ) else 0) ≤
        2 * c * u := by
    intro i hi
    obtain ⟨hpos, hrat⟩ := ratio A T hT1 i hi
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard := card_stage A T i hfit (Finset.mem_Icc.mp hi).1
    have hcard' : (((Finset.univ : Finset (Fin T)).filter
        (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card : ℝ) ≤ A.stageLen T i := by
      exact_mod_cast hcard
    calc (((Finset.univ : Finset (Fin T)).filter
          (fun s : Fin T => A.stageOf T (s : ℕ) = i)).card : ℝ) *
          (c / (A.stageLen T (i - 1) : ℝ))
        ≤ (A.stageLen T i : ℝ) * (c / (A.stageLen T (i - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ ≤ 2 * u * A.stageLen T (i - 1) * (c / (A.stageLen T (i - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hrat (by positivity)
      _ = 2 * c * u := by field_simp
  refine (Finset.sum_le_sum hstage).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : ((A.m + 1 + 1 - 2 : ℕ) : ℝ) = A.m := by
    rw [show A.m + 1 + 1 - 2 = A.m by omega]
  rw [this]
  ring_nf
  exact le_refl _

/-- The first stage has at most `2 T^{1/(m+1)}` periods. -/
theorem card_stage_one (T : ℕ) (hT1 : 1 ≤ T) (hm : 1 ≤ A.m) :
    (((Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = 1)).card : ℝ)
      ≤ 2 * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) := by
  set u := (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hT1) (by positivity)
  have hlen : A.stageStart T 2 = A.ceilLen T 1 := by
    unfold Alg.stageStart
    simp [Alg.stageLen, hm]
  have hc : ((Finset.univ : Finset (Fin T)).filter
      (fun s : Fin T => A.stageOf T (s : ℕ) = 1)).card ≤ A.ceilLen T 1 := by
    have := Finset.card_le_card_of_injOn (fun s : Fin T => (s : ℕ))
      (s := (Finset.univ : Finset (Fin T)).filter (fun s : Fin T => A.stageOf T (s : ℕ) = 1))
      (t := Finset.range (A.ceilLen T 1))
      (fun s hs => by
        have hs' : A.stageOf T (s : ℕ) = 1 := by simpa using hs
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra hge
        push Not at hge
        have hmem : 1 ∈ (Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ (s : ℕ)) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨le_rfl, hm⟩, by rw [hlen]; exact hge⟩
        have hpos := Finset.card_pos.mpr ⟨1, hmem⟩
        unfold Alg.stageOf at hs'
        omega)
      (fun a _ b _ h => Fin.ext h)
    simpa using this
  have hc' : (A.ceilLen T 1 : ℝ) ≤ 2 * u := by
    unfold Alg.ceilLen
    have : (T : ℝ) ^ (((1 : ℕ) : ℝ) / ((A.m : ℝ) + 1)) = u := by rw [hu]; norm_num
    rw [this]
    have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ u)
    linarith
  calc _ ≤ (A.ceilLen T 1 : ℝ) := by exact_mod_cast hc
    _ ≤ 2 * u := hc'

theorem expect_add (z : ℝ) (T : ℕ) (f g : (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => f d + g d) = A.expect z T f + A.expect z T g := by
  unfold Alg.expect
  simp_rw [mul_add]
  exact ENNReal.tsum_add

theorem expect_mono (z : ℝ) (T : ℕ) (f g : (Fin T → ℕ) → ENNReal) (h : ∀ d, f d ≤ g d) :
    A.expect z T f ≤ A.expect z T g := by
  unfold Alg.expect
  exact ENNReal.tsum_le_tsum (fun d => mul_le_mul_right (h d) _)

theorem expect_const_mul (z : ℝ) (T : ℕ) (c : ENNReal) (f : (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => c * f d) = c * A.expect z T f := by
  unfold Alg.expect
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext d; ring

theorem expect_ite (z : ℝ) (T : ℕ) (c : ENNReal) (P : (Fin T → ℕ) → Prop) [DecidablePred P] :
    A.expect z T (fun d => if P d then c else 0) = c * A.prob z T {d | P d} := by
  unfold Alg.expect Alg.prob
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext d
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp [mul_comm]

theorem expect_finsum {ι : Type*} (z : ℝ) (T : ℕ) (I : Finset ι)
    (F : ι → (Fin T → ℕ) → ENNReal) :
    A.expect z T (fun d => ∑ j ∈ I, F j d) = ∑ j ∈ I, A.expect z T (F j) := by
  unfold Alg.expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

end LPC25Aux

open LimitedPriceChanges.AlgorithmI LPCThm1Aux in
theorem solution (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K₁₇ : ℝ, 0 < K₁₇ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ i ∈ Finset.Icc 2 (A.m + 1),
      A.expect z T (fun d =>
          ENNReal.ofReal (S.Gstar A.pstar z - S.G (A.phat T i d) (A.yhat T i d) z)) ≤
        ENNReal.ofReal (K₁₇ / (A.stageLen T (i - 1) : ℝ)) := by
  classical
  obtain ⟨K₃, K₄, K₅, hK₃, hK₄, hK₅, T₀, hP1⟩ := proposition_1 S A z hS hA
  obtain ⟨C, r, hC, hr, hdet⟩ := LPCB1Aux.det_bound (E := ℝ) S.pl S.ph S.Y S.Y_nonempty S.Z S.G
    A.pstar hS.priceSelection z hS.z_mem hS.assumptionA A.yplug hA.plugIn
  have hq1 : Real.exp (-K₄) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq1' : 0 < 1 - Real.exp (-K₄) := by linarith
  refine ⟨C * (1 + K₃ / (1 - Real.exp (-K₄)) + (r ^ 2 + 1) * K₅), by positivity, max T₀ 1,
    fun T hT i hi => ?_⟩
  have hT₀ : T ≥ T₀ := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨hi2, him⟩ := Finset.mem_Icc.mp hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  set n := A.stageLen T (k + 1) with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    unfold Alg.stageLen
    rw [if_pos (by omega)]
    unfold Alg.ceilLen
    have : 0 < (T : ℝ) ^ (((k + 1 : ℕ) : ℝ) / ((A.m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hT1) _
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr this))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set N := ⌈(n : ℝ) * r ^ 2⌉₊ with hN
  let Sj : ℕ → Set (Fin T → ℕ) := fun j =>
    {d | Real.sqrt ((j : ℝ) / n) ≤ |z - A.zhat T (k + 1) d|}
  -- pointwise bound
  have hpt : ∀ d, ENNReal.ofReal (S.Gstar A.pstar z -
      S.G (A.phat T (k + 2) d) (A.yhat T (k + 2) d) z) ≤
      ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N,
        (if d ∈ Sj j then ENNReal.ofReal (C / n) else 0) := by
    intro d
    have hz : A.zhat T (k + 1) d ∈ S.Z := (hA.mle _ (phat_mem A z hS hA T (k + 1) d) _).1
    have h1 := hdet _ hz
    have heta : ‖A.zhat T (k + 1) d - z‖ = |z - A.zhat T (k + 1) d| := by
      rw [Real.norm_eq_abs, abs_sub_comm]
    rw [heta] at h1
    have h2 := LPCB1Aux.grid_bound n hn1 r |z - A.zhat T (k + 1) d| (abs_nonneg _)
    have hrhs : ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N,
        (if d ∈ Sj j then ENNReal.ofReal (C / n) else 0) =
        ENNReal.ofReal (C * (1 / (n : ℝ) + ∑ j ∈ Finset.Icc 1 N,
          (1 / (n : ℝ)) * (if Real.sqrt ((j : ℝ) / n) ≤ |z - A.zhat T (k + 1) d| then 1 else 0))) := by
      rw [mul_add, Finset.mul_sum, ENNReal.ofReal_add (by positivity)
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)]
      congr 1
      · congr 1; ring
      · apply Finset.sum_congr rfl
        intro j _
        simp only [Sj, Set.mem_ofPred_eq]
        split_ifs <;> simp [div_eq_mul_inv]
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    have : A.phat T (k + 2) d = A.pstar (A.yplug (A.zhat T (k + 1) d)) (A.zhat T (k + 1) d) := rfl
    have hy : A.yhat T (k + 2) d = A.yplug (A.zhat T (k + 1) d) := rfl
    rw [this, hy]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC.le)
  refine (LPC25Aux.expect_mono A z T _ _ hpt).trans ?_
  rw [LPC25Aux.expect_add, LPC25Aux.expect_finsum]
  have hconst : A.expect z T (fun _ => ENNReal.ofReal (C / n)) = ENNReal.ofReal (C / n) := by
    unfold Alg.expect
    rw [ENNReal.tsum_mul_right, mass_one A z hS hA T, one_mul]
  rw [hconst]
  have hj : ∀ j ∈ Finset.Icc 1 N,
      A.expect z T (fun d => if d ∈ Sj j then ENNReal.ofReal (C / n) else 0) ≤
      ENNReal.ofReal (C / n) * ENNReal.ofReal
        (K₃ * Real.exp (-((n : ℝ) * K₄ * Real.sqrt ((j : ℝ) / n) ^ 2)) + K₅ / n) := by
    intro j hjm
    rw [LPC25Aux.expect_ite A z T (ENNReal.ofReal (C / n)) (fun d => d ∈ Sj j)]
    gcongr
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hjm).1
    have := hP1 T hT₀ (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) _
      (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (j : ℝ) / n))
    have hset : {d | d ∈ Sj j} = {d | Real.sqrt ((j : ℝ) / n) ≤ |z - A.zhat T (k + 1) d|} := rfl
    rw [hset]
    refine this.trans (le_of_eq ?_)
    rw [hn]
    congr 3
    ring
  refine (add_le_add (le_refl _) (Finset.sum_le_sum hj)).trans ?_
  simp_rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C / n)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity),
    ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun j _ => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  exact LPCB1Aux.real_sum_bound n hn1 C r K₃ K₄ K₅ hC hK₃ hK₄ hK₅

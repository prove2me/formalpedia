-- Prove2me | solution 1 for LimitedPriceChanges.AlgorithmI.theorem_B1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:49:18.888195+00:00
-- url     : https://prove2.me/submissions/57be6071-23d5-480b-b0b5-2699a830070b

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_DataBasedOptimization

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

open LimitedPriceChanges.AlgorithmI MeasureTheory in
theorem solution {k : ℕ} (pl ph : ℝ) (Y : Finset ℕ) (hY : Y.Nonempty)
    (Z : Set (EuclideanSpace ℝ (Fin k))) (hZc : IsCompact Z) (hZv : Convex ℝ Z)
    (G : ℝ → ℕ → EuclideanSpace ℝ (Fin k) → ℝ) (pstar : ℕ → EuclideanSpace ℝ (Fin k) → ℝ)
    (hsel : IsPriceSelection pl ph Y Z G pstar)
    (z : EuclideanSpace ℝ (Fin k)) (hz : z ∈ Z) (hA : AssumptionA pl ph Y hY Z G pstar z)
    (ysel : EuclideanSpace ℝ (Fin k) → ℕ) (hysel : IsLevelSelection Y Z G pstar ysel)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (zhat : ℕ → Ω → EuclideanSpace ℝ (Fin k)) (hmeas : ∀ n, Measurable (zhat n))
    (hzZ : ∀ n ω, zhat n ω ∈ Z)
    (hGmeas : ∀ n, Measurable (fun ω => G (pstar (ysel (zhat n ω)) (zhat n ω)) (ysel (zhat n ω)) z))
    (K₁₄ K₁₅ K₁₆ : ℝ) (hK₁₄ : 0 < K₁₄) (hK₁₅ : 0 < K₁₅) (hK₁₆ : 0 < K₁₆)
    (h10 : ∀ n : ℕ, 1 ≤ n → ∀ ϵ : ℝ, 0 < ϵ →
      P {ω | ϵ ≤ ‖zhat n ω - z‖} ≤
        ENNReal.ofReal (K₁₄ * Real.exp (-((n : ℝ) * K₁₅ * ϵ ^ 2)) + K₁₆ / (n : ℝ))) :
    ∃ K₁₇ : ℝ, 0 < K₁₇ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∫⁻ ω, ENNReal.ofReal (optValue Y hY G pstar z -
          G (pstar (ysel (zhat n ω)) (zhat n ω)) (ysel (zhat n ω)) z) ∂P ≤
        ENNReal.ofReal (K₁₇ / (n : ℝ)) := by
  obtain ⟨C, r, hC, hr, hdet⟩ :=
    LPCB1Aux.det_bound pl ph Y hY Z G pstar hsel z hz hA ysel hysel
  have hq1 : Real.exp (-K₁₅) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq1' : 0 < 1 - Real.exp (-K₁₅) := by linarith
  refine ⟨C * (1 + K₁₄ / (1 - Real.exp (-K₁₅)) + (r ^ 2 + 1) * K₁₆), by positivity, 1,
    fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set N := ⌈(n : ℝ) * r ^ 2⌉₊ with hN
  let S : ℕ → Set Ω := fun j => {ω | Real.sqrt ((j : ℝ) / n) ≤ ‖zhat n ω - z‖}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    measurableSet_le measurable_const ((hmeas n).sub_const z).norm
  -- pointwise bound
  have hpt : ∀ ω, ENNReal.ofReal (optValue Y hY G pstar z -
      G (pstar (ysel (zhat n ω)) (zhat n ω)) (ysel (zhat n ω)) z) ≤
      ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N,
        (S j).indicator (fun _ => ENNReal.ofReal (C / n)) ω := by
    intro ω
    have h1 := hdet _ (hzZ n ω)
    have h2 := LPCB1Aux.grid_bound n hn r ‖zhat n ω - z‖ (norm_nonneg _)
    have hrhs : ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N,
        (S j).indicator (fun _ => ENNReal.ofReal (C / n)) ω =
        ENNReal.ofReal (C * (1 / (n : ℝ) + ∑ j ∈ Finset.Icc 1 N,
          (1 / (n : ℝ)) * (if Real.sqrt ((j : ℝ) / n) ≤ ‖zhat n ω - z‖ then 1 else 0))) := by
      rw [mul_add, Finset.mul_sum, ENNReal.ofReal_add (by positivity)
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)]
      congr 1
      · congr 1; ring
      · apply Finset.sum_congr rfl
        intro j _
        simp only [Set.indicator_apply, S, Set.mem_ofPred_eq]
        split_ifs <;> simp [div_eq_mul_inv]
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC.le)
  calc ∫⁻ ω, ENNReal.ofReal (optValue Y hY G pstar z -
          G (pstar (ysel (zhat n ω)) (zhat n ω)) (ysel (zhat n ω)) z) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N,
        (S j).indicator (fun _ => ENNReal.ofReal (C / n)) ω) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N, ENNReal.ofReal (C / n) * P (S j) := by
      rw [lintegral_add_left measurable_const, lintegral_finset_sum _ (fun j _ =>
        measurable_const.indicator (hSm j))]
      simp only [lintegral_indicator_const (hSm _), lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (C / n) + ∑ j ∈ Finset.Icc 1 N, ENNReal.ofReal (C / n) *
        ENNReal.ofReal (K₁₄ * Real.exp (-((n : ℝ) * K₁₅ * Real.sqrt ((j : ℝ) / n) ^ 2)) +
          K₁₆ / n) := by
      gcongr with j hj
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      exact h10 n hn _ (Real.sqrt_pos.mpr (by positivity))
    _ = ENNReal.ofReal (C / n + ∑ j ∈ Finset.Icc 1 N, C / n *
        (K₁₄ * Real.exp (-((n : ℝ) * K₁₅ * Real.sqrt ((j : ℝ) / n) ^ 2)) + K₁₆ / n)) := by
      rw [ENNReal.ofReal_add (by positivity)
        (Finset.sum_nonneg (fun j _ => by positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C * (1 + K₁₄ / (1 - Real.exp (-K₁₅)) + (r ^ 2 + 1) * K₁₆) / n) :=
      ENNReal.ofReal_le_ofReal (LPCB1Aux.real_sum_bound n hn C r K₁₄ K₁₅ K₁₆ hC hK₁₄ hK₁₅ hK₁₆)

-- Prove2me | solution 1 for LimitedPriceChanges.AlgorithmI.eq_26
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:19:51.136809+00:00
-- url     : https://prove2.me/submissions/fc13122e-0f8c-486c-bf1b-0e78334f8ae0
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
theorem det_opt {E : Type*} [NormedAddCommGroup E] (pl ph : ℝ) (Y : Finset ℕ)
    (hY : Y.Nonempty) (Z : Set E) (G : ℝ → ℕ → E → ℝ) (pstar : ℕ → E → ℝ)
    (hsel : IsPriceSelection pl ph Y Z G pstar) (z : E) (hz : z ∈ Z)
    (hA : AssumptionA pl ph Y hY Z G pstar z) (ysel : E → ℕ)
    (hysel : IsLevelSelection Y Z G pstar ysel) :
    ∃ r : ℝ, 0 < r ∧ ∀ zh ∈ Z, ‖zh - z‖ < r →
      G (pstar (ysel zh) z) (ysel zh) z = optValue Y hY G pstar z := by
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
  refine ⟨r, hrpos, fun zh hzh hclose0 => ?_⟩
  clear_value opt
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ‖zh - z‖ := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := hη ▸ norm_nonneg _
  have hyh : ysel zh ∈ Y := (hysel zh hzh).1
  have hclose : η < r := by rw [hη]; exact hclose0
  all_goals
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
    rw [hyopt]

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

namespace LPC26Aux

open LimitedPriceChanges.AlgorithmI LPCThm1Aux

variable {S : Model} (A : Alg S)

theorem yhat_succ (T k : ℕ) (d : Fin T → ℕ) :
    A.yhat T (k + 2) d = A.yplug (A.zhat T (k + 1) d) := rfl

theorem phat_succ (T k : ℕ) (d : Fin T → ℕ) :
    A.phat T (k + 2) d = A.pstar (A.yplug (A.zhat T (k + 1) d)) (A.zhat T (k + 1) d) := rfl

theorem zhat_mem (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) (T i : ℕ)
    (d : Fin T → ℕ) : A.zhat T i d ∈ S.Z :=
  (hA.mle _ (phat_mem A z hS hA T i d) _).1

/-- Near `z`, the plug-in level is optimal at `z`, hence exceeds `dl`. -/
theorem near_opt (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) :
    ∃ r : ℝ, 0 < r ∧ ∀ zh ∈ S.Z, |zh - z| < r → S.dl < A.yplug zh := by
  obtain ⟨r, hr, h⟩ := LPCB1Aux.det_opt (E := ℝ) S.pl S.ph S.Y S.Y_nonempty S.Z S.G A.pstar
    hS.priceSelection z hS.z_mem hS.assumptionA A.yplug hA.plugIn
  refine ⟨r, hr, fun zh hzh hlt => ?_⟩
  have hopt := h zh hzh (by simpa [Real.norm_eq_abs] using hlt)
  exact hS.optLevel _ ((hA.plugIn zh hzh).1) hopt

theorem prob_mono (z : ℝ) (T : ℕ) (E F : Set (Fin T → ℕ)) (h : E ⊆ F) :
    A.prob z T E ≤ A.prob z T F := by
  unfold Alg.prob
  exact ENNReal.tsum_le_tsum (fun d => Set.indicator_le_indicator_of_subset h (fun _ => zero_le) d)

end LPC26Aux

open LimitedPriceChanges.AlgorithmI LPCThm1Aux LPC26Aux in
theorem solution (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ i ∈ Finset.Icc 2 (A.m + 1),
      A.prob z T {d | A.yhat T i d ≠ A.ytilde T i d} ≤
        ENNReal.ofReal (K / (A.stageLen T (i - 1) : ℝ)) := by
  obtain ⟨K₃, K₄, K₅, hK₃, hK₄, hK₅, T₀, hP1⟩ := proposition_1 S A z hS hA
  obtain ⟨r, hr, hnear⟩ := near_opt A z hS hA
  refine ⟨K₃ / (K₄ * r ^ 2) + K₅, by positivity, max T₀ 1, fun T hT i hi => ?_⟩
  have hT₀ : T ≥ T₀ := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨hi2, him⟩ := Finset.mem_Icc.mp hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  have hsub : {d | A.yhat T (k + 2) d ≠ A.ytilde T (k + 2) d} ⊆
      {d | r ≤ |z - A.zhat T (k + 1) d|} := by
    intro d hd
    simp only [Set.mem_setOf_eq] at hd ⊢
    by_contra hlt
    push Not at hlt
    have hz := zhat_mem A z hS hA T (k + 1) d
    have hdl := hnear _ hz (by rw [abs_sub_comm]; exact hlt)
    apply hd
    unfold Alg.ytilde Alg.ytildeOf
    rw [← yhat_succ] at hdl
    rw [if_pos hdl]
  refine (prob_mono A z T _ _ hsub).trans ?_
  have hmem : k + 1 ∈ Finset.Icc 1 (A.m + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  refine (hP1 T hT₀ (k + 1) hmem r hr).trans ?_
  rw [show k + 2 - 1 = k + 1 by omega]
  apply ENNReal.ofReal_le_ofReal
  -- `I_{k+1} ≥ 1`
  set n : ℝ := (A.stageLen T (k + 1) : ℝ) with hn
  have hnpos : 0 < n := by
    rw [hn]
    unfold Alg.stageLen
    rw [if_pos (by omega)]
    unfold Alg.ceilLen
    have : 0 < (T : ℝ) ^ (((k + 1 : ℕ) : ℝ) / ((A.m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hT1) _
    exact_mod_cast Nat.ceil_pos.mpr this
  have hexp : Real.exp (-(K₄ * n * r ^ 2)) ≤ 1 / (K₄ * n * r ^ 2) := by
    have hx : 0 < K₄ * n * r ^ 2 := by positivity
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le hx
    linarith [Real.add_one_le_exp (K₄ * n * r ^ 2)]
  have : K₃ * Real.exp (-(K₄ * n * r ^ 2)) ≤ K₃ / (K₄ * r ^ 2) / n := by
    calc K₃ * Real.exp (-(K₄ * n * r ^ 2)) ≤ K₃ * (1 / (K₄ * n * r ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp hK₃.le
      _ = K₃ / (K₄ * r ^ 2) / n := by field_simp
  calc K₃ * Real.exp (-(K₄ * n * r ^ 2)) + K₅ / n ≤ K₃ / (K₄ * r ^ 2) / n + K₅ / n := by
        linarith
    _ = (K₃ / (K₄ * r ^ 2) + K₅) / n := by ring

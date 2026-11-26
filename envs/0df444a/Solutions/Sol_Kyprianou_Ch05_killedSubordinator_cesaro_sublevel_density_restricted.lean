-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density_restricted
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:05:59.237658+00:00
-- url     : https://prove2.me/submissions/30cad51a-eec0-4b85-9f7c-0a1e622862fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_restrictedExponent_bohr_mean
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_restrictedExponent_bohr_second_moment
import Theorems.Thm_pz_cesaro_density_bound
import Theorems.Thm_cosine_sublevel_density
import Theorems.Thm_Kyprianou_Ch05_atom_mass_extraction
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ K : Real, ∀ ρ : ENNReal, 0 < ρ →
      ∃ δ : Real, 0 < δ ∧ δ ≤ 1 ∧ ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ) := by
  intro hPi K ρ hρ
  have hLevy : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi) < ⊤ := hTriplet.2.2.2.1
  -- Pi (Ioi 1) is finite, via the Levy integrability field
  have hIoi1 : Pi (Set.Ioi (1 : Real)) < ⊤ := by
    have hpt : ∀ y ∈ Set.Ioi (1 : Real), ENNReal.ofReal (min 1 y) = 1 := by
      intro y hy
      rw [min_eq_left (le_of_lt hy), ENNReal.ofReal_one]
    have h1 : (∫⁻ y in Set.Ioi (1 : Real), ENNReal.ofReal (min 1 y) ∂Pi) = Pi (Set.Ioi 1) := by
      rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt)),
        lintegral_const, Measure.restrict_apply_univ, one_mul]
    calc Pi (Set.Ioi 1) = ∫⁻ y in Set.Ioi (1 : Real), ENNReal.ofReal (min 1 y) ∂Pi := h1.symm
    _ ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
        lintegral_mono_set (Set.Ioi_subset_Ioi (by norm_num))
    _ < ⊤ := hLevy
  -- Pi (Icc δ 1) is finite for 0 < δ ≤ 1
  have hfinIcc : ∀ δ : Real, 0 < δ → δ ≤ 1 → Pi (Set.Icc δ 1) < ⊤ := by
    intro δ hδ hδ1
    have hstep : ENNReal.ofReal δ * Pi (Set.Icc δ 1)
        ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi := by
      calc ENNReal.ofReal δ * Pi (Set.Icc δ 1)
          = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal δ ∂Pi := by
            rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
              (Eventually.of_forall (fun y hy => ENNReal.ofReal_le_ofReal (le_min hδ1 hy.1))))
      _ ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_set (fun y hy => lt_of_lt_of_le hδ hy.1)
    by_contra htop
    have htop' : Pi (Set.Icc δ 1) = ⊤ := top_unique (not_lt.mp htop)
    rw [htop', ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))] at hstep
    exact lt_irrefl _ (lt_of_le_of_lt hstep hLevy)
  -- trivial case ρ = ⊤
  by_cases hρtop : ρ = ⊤
  · subst hρtop
    exact ⟨1 / 2, by norm_num, by norm_num, 0, fun U _ => le_top⟩
  -- trivial case K < 0 : the sublevel set is empty since R̃ ≥ 0
  by_cases hK : (0 : Real) ≤ K
  swap
  · have hKlt : K < 0 := not_le.mp hK
    refine ⟨1 / 2, by norm_num, by norm_num, 0, fun U _ => ?_⟩
    have hpt : ∀ u : Real, ENNReal.ofReal (if (∫⁻ y in Set.Icc (1 / 2 : Real) 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) = 0 := by
      intro u
      have hneg : ¬ (∫⁻ y in Set.Icc (1 / 2 : Real) 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K :=
        not_le.mpr (lt_of_lt_of_le hKlt ENNReal.toReal_nonneg)
      rw [if_neg hneg, ENNReal.ofReal_zero]
    have hzero : (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Icc (1 / 2 : Real) 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) ∂volume) = 0 := by
      apply le_antisymm _ bot_le
      calc (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Icc (1 / 2 : Real) 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) ∂volume)
          ≤ ∫⁻ u in Set.Icc (0 : Real) U, (0 : ℝ≥0∞) ∂volume := lintegral_mono (fun u => (hpt u).le)
      _ = 0 := lintegral_zero
    rw [hzero, zero_mul]
    exact bot_le
  -- main case: 0 ≤ K and ρ ≠ ⊤
  have hρpos : 0 < ρ.toReal := ENNReal.toReal_pos hρ.ne' hρtop
  obtain ⟨M, hM⟩ := pz_cesaro_density_bound K hK ρ.toReal hρpos
  obtain ⟨M₄, hM₄⟩ := cosine_sublevel_density K ρ hρ
  set T : Real := max (max M ((2 * M₄) ^ 2)) 1 with hTdef
  have hT1 : (1 : Real) ≤ T := le_max_right _ _
  have hTM : M ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hT4 : (2 * M₄) ^ 2 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  -- Pi (Ioc 0 1) = ⊤
  have hIoc : Pi (Set.Ioc (0 : Real) 1) = ⊤ := by
    have hunion : Pi (Set.Ioi (0 : Real)) = Pi (Set.Ioc 0 1) + Pi (Set.Ioi 1) := by
      conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : Real) ≤ 1 by norm_num)]
      rw [measure_union (by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact not_lt.mpr hx1.2 hx2) measurableSet_Ioi]
    rw [hPi] at hunion
    by_contra hne
    have hlt : Pi (Set.Ioc 0 1) + Pi (Set.Ioi 1) < ⊤ :=
      ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, hIoi1⟩
    rw [← hunion] at hlt
    exact lt_irrefl _ hlt
  -- choose n with Pi (Icc (1/(n+1)) 1) ≥ ofReal T, by continuity from below
  have hchoose : ∃ n : ℕ, ENNReal.ofReal T ≤ Pi (Set.Icc (1 / ((n : Real) + 1)) 1) := by
    have hmono : Monotone (fun n : ℕ => Set.Icc (1 / ((n : Real) + 1)) 1) := by
      intro a b hab
      apply Set.Icc_subset_Icc _ le_rfl
      apply one_div_le_one_div_of_le
      · have hnn : (0 : Real) ≤ (a : Real) := Nat.cast_nonneg a
        linarith
      · have h1 : (a : Real) ≤ (b : Real) := by exact_mod_cast hab
        linarith
    have hunionS : ⋃ n : ℕ, Set.Icc (1 / ((n : Real) + 1)) 1 = Set.Ioc (0 : Real) 1 := by
      apply Set.Subset.antisymm
      · apply Set.iUnion_subset
        intro n x hx
        exact ⟨lt_of_lt_of_le (by positivity) hx.1, hx.2⟩
      · intro x hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx.1
        exact Set.mem_iUnion.mpr ⟨n, hn.le, hx.2⟩
    have hmeas : Pi (⋃ n : ℕ, Set.Icc (1 / ((n : Real) + 1)) 1)
        = ⨆ n : ℕ, Pi (Set.Icc (1 / ((n : Real) + 1)) 1) := hmono.measure_iUnion
    rw [hunionS, hIoc] at hmeas
    by_contra hcon
    push_neg at hcon
    have hle : ⨆ n : ℕ, Pi (Set.Icc (1 / ((n : Real) + 1)) 1) ≤ ENNReal.ofReal T :=
      ciSup_le (fun n => (hcon n).le)
    rw [← hmeas] at hle
    exact not_le_of_gt ENNReal.ofReal_lt_top hle
  obtain ⟨n, hn⟩ := hchoose
  set δ : Real := 1 / ((n : Real) + 1) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    have hnn : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    rw [hδdef, div_le_one (by linarith : (0 : Real) < (n : Real) + 1)]
    linarith
  have hfin : Pi (Set.Icc δ 1) < ⊤ := hfinIcc δ hδ hδ1
  set Λ : Real := (Pi (Set.Icc δ 1)).toReal with hΛdef
  have hΛnn : 0 ≤ Λ := ENNReal.toReal_nonneg
  have hΛT : T ≤ Λ := by
    have h2 : (ENNReal.ofReal T).toReal ≤ (Pi (Set.Icc δ 1)).toReal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin.ne).mpr hn
    rw [← hΛdef] at h2
    rwa [ENNReal.toReal_ofReal (zero_le_one.trans hT1)] at h2
  have hΛM : M ≤ Λ := hTM.trans hΛT
  have hΛ1 : (1 : Real) ≤ Λ := hT1.trans hΛT
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ1
  set A : Real := (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal with hAdef
  have hAnn : 0 ≤ A := ENNReal.toReal_nonneg
  have hAfin : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi)
        ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal Λ ∂Pi := by
          apply lintegral_mono_ae
          apply (ae_restrict_iff' measurableSet_Icc).mpr
          apply Eventually.of_forall
          intro y hy
          apply ENNReal.ofReal_le_ofReal
          have hle : Pi {y} ≤ Pi (Set.Icc δ 1) := measure_mono (Set.singleton_subset_iff.mpr hy)
          exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin.ne hle) hfin.ne).mpr hle
    _ = ENNReal.ofReal Λ * Pi (Set.Icc δ 1) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  -- the restricted measure is finite (an SFinite instance for Tonelli below)
  have hfinμ : IsFiniteMeasure (Pi.restrict (Set.Icc δ 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  -- measurability of the restricted exponent in u (Tonelli; integrand jointly continuous)
  have hRmeas : Measurable (fun u => (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) := by
    have hcont : Continuous (fun p : Real × Real => (1 : Real) - Real.cos (p.1 * p.2)) :=
      continuous_const.sub (Real.continuous_cos.comp (continuous_fst.mul continuous_snd))
    have hF : Measurable (fun p : Real × Real => ENNReal.ofReal (1 - Real.cos (p.1 * p.2))) :=
      (ENNReal.continuous_ofReal.comp hcont).measurable
    exact (hF.lintegral_prod_right').ennreal_toReal
  -- pointwise bound and finiteness for the ENNReal exponent integral
  have hRleE : ∀ u : Real, (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
      ≤ ENNReal.ofReal 2 * Pi (Set.Icc δ 1) := by
    intro u
    calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
        ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal 2 ∂Pi := by
          apply lintegral_mono
          intro y
          apply ENNReal.ofReal_le_ofReal
          have h := Real.neg_one_le_cos (u * y)
          linarith
    _ = ENNReal.ofReal 2 * Pi (Set.Icc δ 1) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  have hRfin : ∀ u : Real, (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi) ≠ ⊤ :=
    fun u => ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) (hRleE u)
  have hRle2 : ∀ u : Real, (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ 2 * Λ := by
    intro u
    have h := (ENNReal.toReal_le_toReal (hRfin u)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)).mpr (hRleE u)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)] at h
  have h12ne : (1 / 2 : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ENNReal.half_le_self
  refine ⟨δ, hδ, hδ1, ?_⟩
  rcases le_total A (Λ * Real.sqrt Λ) with hcase | hcase
  · -- CASE 1: A ≤ Λ * sqrt Λ. Paley–Zygmund via the Bohr moments D1, D2 and the real step D3.
    obtain ⟨U0₁, hU0₁⟩ := Kyprianou.Ch05.killedSubordinator_restrictedExponent_bohr_mean
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi δ hδ hδ1 1 zero_lt_one
    obtain ⟨U0₂, hU0₂⟩ := Kyprianou.Ch05.killedSubordinator_restrictedExponent_bohr_second_moment
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi δ hδ hδ1 1 zero_lt_one
    rw [← hΛdef] at hU0₁ hU0₂
    rw [← hAdef] at hU0₂
    have hind₁ : Measurable (fun u => ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0)) := by
      classical
      have hset : MeasurableSet {u : Real | (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K} := measurableSet_le hRmeas measurable_const
      have h : Measurable (fun u => if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) :=
        Measurable.piecewise hset (measurable_const : Measurable (fun _ : Real => (1 : Real)))
          (measurable_const : Measurable (fun _ : Real => (0 : Real)))
      exact ENNReal.measurable_ofReal.comp h
    have hind₂ : Measurable (fun u => ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then (1 : Real) else 0)) := by
      classical
      have hset : MeasurableSet {u : Real | K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal} := measurableSet_lt measurable_const hRmeas
      have h : Measurable (fun u => if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then (1 : Real) else 0) :=
        Measurable.piecewise hset (measurable_const : Measurable (fun _ : Real => (1 : Real)))
          (measurable_const : Measurable (fun _ : Real => (0 : Real)))
      exact ENNReal.measurable_ofReal.comp h
    have hR1meas : Measurable (fun u => ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) := ENNReal.measurable_ofReal.comp hRmeas
    have hR2meas : Measurable (fun u => ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hRmeas.pow_const 2)
    refine ⟨max (max U0₁ U0₂) 1, fun W hW => ?_⟩
    have hW1 : U0₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
    have hW2 : U0₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
    have hWge : (1 : Real) ≤ W := (le_max_right _ _).trans hW
    obtain ⟨haU1, haU2⟩ := hU0₁ W hW1
    have hbU := hU0₂ W hW2
    have hV0 : ENNReal.ofReal W ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hWge))
    have hVt : ENNReal.ofReal W ≠ ⊤ := ENNReal.ofReal_ne_top
    have hInt1 : (∫⁻ u in Set.Icc (0 : Real) W, (1 : ℝ≥0∞) ∂volume) = ENNReal.ofReal W := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, one_mul]
    have hDDC : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
        + (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
        = ENNReal.ofReal W := by
      rw [← lintegral_add_left' hind₁.aemeasurable, ← hInt1]
      apply lintegral_congr
      intro u
      by_cases h : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K
      · rw [if_pos h, if_neg (not_lt.mpr h), ENNReal.ofReal_one, ENNReal.ofReal_zero, add_zero]
      · rw [if_neg h, if_pos (not_le.mp h), ENNReal.ofReal_one, ENNReal.ofReal_zero, zero_add]
    have hDDle : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
        ≤ ENNReal.ofReal W := by
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
          ≤ ∫⁻ u in Set.Icc (0 : Real) W, (1 : ℝ≥0∞) ∂volume := by
            apply lintegral_mono
            intro u
            by_cases h : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K <;> simp [h]
      _ = ENNReal.ofReal W := hInt1
    have hDCle : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
        ≤ ENNReal.ofReal W := by
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
          ≤ ∫⁻ u in Set.Icc (0 : Real) W, (1 : ℝ≥0∞) ∂volume := by
            apply lintegral_mono
            intro u
            by_cases h : K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal <;> simp [h]
      _ = ENNReal.ofReal W := hInt1
    have hdU1 : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
        * (ENNReal.ofReal W)⁻¹ ≤ 1 :=
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
          * (ENNReal.ofReal W)⁻¹
          ≤ ENNReal.ofReal W * (ENNReal.ofReal W)⁻¹ := mul_le_mul hDDle le_rfl bot_le bot_le
      _ = 1 := ENNReal.mul_inv_cancel hV0 hVt
    have hdcU1 : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
        * (ENNReal.ofReal W)⁻¹ ≤ 1 :=
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
          * (ENNReal.ofReal W)⁻¹
          ≤ ENNReal.ofReal W * (ENNReal.ofReal W)⁻¹ := mul_le_mul hDCle le_rfl bot_le bot_le
      _ = 1 := ENNReal.mul_inv_cancel hV0 hVt
    have hsumN : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
        * (ENNReal.ofReal W)⁻¹
        + (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
        * (ENNReal.ofReal W)⁻¹ = 1 := by
      rw [← add_mul, hDDC, ENNReal.mul_inv_cancel hV0 hVt]
    have haUfin : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume)
        * (ENNReal.ofReal W)⁻¹ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩) haU1
    have hbUfin : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume)
        * (ENNReal.ofReal W)⁻¹ ≠ ⊤ := by
      have hI2 : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume)
          ≤ ENNReal.ofReal ((2 * Λ) ^ 2) * ENNReal.ofReal W := by
        calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume)
            ≤ ∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((2 * Λ) ^ 2) ∂volume := by
              apply lintegral_mono
              intro u
              apply ENNReal.ofReal_le_ofReal
              exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hRle2 u) 2
        _ = ENNReal.ofReal ((2 * Λ) ^ 2) * ENNReal.ofReal W := by
              rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹
          ≤ (ENNReal.ofReal ((2 * Λ) ^ 2) * ENNReal.ofReal W) * (ENNReal.ofReal W)⁻¹ :=
            mul_le_mul hI2 le_rfl bot_le bot_le
      _ = ENNReal.ofReal ((2 * Λ) ^ 2) := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hV0 hVt, mul_one]
    -- split of the first Cesaro integral along the sublevel set
    have hsplit : ∀ u : Real, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal
        = ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0)
        + ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) := by
      intro u
      by_cases h : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K
      · rw [if_pos h, if_neg (not_lt.mpr h)]
        simp only [ENNReal.ofReal_one, ENNReal.ofReal_zero, mul_one, mul_zero, add_zero]
      · rw [if_neg h, if_pos (not_le.mp h)]
        simp only [ENNReal.ofReal_one, ENNReal.ofReal_zero, mul_one, mul_zero, zero_add]
    have hI1 : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume)
        = (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
        + (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) := by
      have hfg₁ : Measurable (fun u => ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0)) := hR1meas.mul hind₁
      rw [← lintegral_add_left' hfg₁.aemeasurable]
      apply lintegral_congr
      intro u
      exact hsplit u
    have haUeq : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹
        = (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
        + (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹ := by
      rw [hI1, add_mul]
    have hP1 : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
        ≤ ENNReal.ofReal K * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) := by
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)
          ≤ ∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal K * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume := by
            apply lintegral_mono
            intro u
            by_cases h : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K
            · have e : ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) = 1 := by
                rw [if_pos h]; exact ENNReal.ofReal_one
              simp only [e, mul_one]
              exact ENNReal.ofReal_le_ofReal h
            · have e : ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) = 0 := by
                rw [if_neg h]; exact ENNReal.ofReal_zero
              simp [e]
      _ = ENNReal.ofReal K * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) :=
            lintegral_const_mul _ hind₁
    have hP1N : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
        ≤ ENNReal.ofReal K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹) := by
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
          ≤ (ENNReal.ofReal K * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume)) * (ENNReal.ofReal W)⁻¹ :=
            mul_le_mul hP1 le_rfl bot_le bot_le
      _ = ENNReal.ofReal K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹) :=
            mul_assoc _ _ _
    -- the AM-GM bound on the superlevel part, for every c > 0
    have hP2 : ∀ c : Real, 0 < c →
        (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
        ≤ ENNReal.ofReal (1 / (2 * c)) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume)
        + ENNReal.ofReal (c / 2) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) := by
      intro c hc
      have h2c : (0 : Real) < 2 * c := by linarith
      have hfg₂ : Measurable (fun u => ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0)) :=
        (ENNReal.measurable_ofReal.comp ((hRmeas.pow_const 2).div_const (2 * c))).mul hind₂
      have hpt : ∀ u : Real, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0)
          ≤ ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0)
          + ENNReal.ofReal (c / 2) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) := by
        intro u
        by_cases h : K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal
        · rw [if_pos h]
          simp only [ENNReal.ofReal_one, mul_one]
          rw [← ENNReal.ofReal_add (div_nonneg (sq_nonneg _) h2c.le) (by linarith : (0 : Real) ≤ c / 2)]
          apply ENNReal.ofReal_le_ofReal
          have hsq : (2 * c) * (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2 + c ^ 2 := by nlinarith [sq_nonneg ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal - c)]
          calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal = (2 * c) * (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal / (2 * c) := (mul_div_cancel_left₀ _ h2c.ne').symm
          _ ≤ ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2 + c ^ 2) / (2 * c) := (div_le_div_iff_of_pos_right h2c).mpr hsq
          _ = (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2 / (2 * c) + c / 2 := by field_simp <;> ring
        · simp [if_neg h]
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
          ≤ ∫⁻ u in Set.Icc (0 : Real) W, (ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0)
            + ENNReal.ofReal (c / 2) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0)) ∂volume :=
            lintegral_mono hpt
      _ = (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)
          + (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (c / 2) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) :=
            lintegral_add_left' hfg₂.aemeasurable _
      _ ≤ (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) ∂volume)
          + ENNReal.ofReal (c / 2) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) := by
            apply add_le_add _ (lintegral_const_mul _ hind₂).le
            apply lintegral_mono
            intro u
            calc ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0)
                ≤ ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) * 1 := by
                  apply mul_le_mul le_rfl _ bot_le bot_le
                  by_cases h : K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal <;> simp [h]
            _ = ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) / (2 * c)) := mul_one _
      _ = ENNReal.ofReal (1 / (2 * c)) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume)
          + ENNReal.ofReal (c / 2) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) := by
            congr 1
            rw [← lintegral_const_mul _ hR2meas]
            apply lintegral_congr
            intro u
            rw [← ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ 1 / (2 * c))]
            congr 1
            rw [mul_comm (1 / (2 * c)) ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2), mul_one_div]
    have hP2N : ∀ c : Real, 0 < c →
        (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
        ≤ ENNReal.ofReal (1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹)
        + ENNReal.ofReal (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹) := by
      intro c hc
      calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal * ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
          ≤ (ENNReal.ofReal (1 / (2 * c)) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume)
            + ENNReal.ofReal (c / 2) * (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume)) * (ENNReal.ofReal W)⁻¹ :=
            mul_le_mul (hP2 c hc) le_rfl bot_le bot_le
      _ = ENNReal.ofReal (1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + ENNReal.ofReal (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹) := by
            rw [add_mul, mul_assoc, mul_assoc]
    -- convert the ENNReal Cesaro bounds to real inequalities
    have hα1 : Λ - 1 ≤ ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := by
      have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨haUfin, ENNReal.one_ne_top⟩)).mpr haU2
      rw [ENNReal.toReal_ofReal hΛnn, ENNReal.toReal_add haUfin ENNReal.one_ne_top, ENNReal.toReal_one] at h
      linarith
    have hβ : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        ≤ Λ ^ 2 + A / 2 + 1 := by
      have hRHSfin : ENNReal.ofReal (Λ ^ 2) + (1 / 2 : ℝ≥0∞) * ENNReal.ofReal A + 1 ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
          ENNReal.mul_ne_top h12ne ENNReal.ofReal_ne_top⟩, ENNReal.one_ne_top⟩
      have h := (ENNReal.toReal_le_toReal hbUfin hRHSfin).mpr hbU
      have e : (ENNReal.ofReal (Λ ^ 2) + (1 / 2 : ℝ≥0∞) * ENNReal.ofReal A + 1).toReal
          = Λ ^ 2 + A / 2 + 1 := by
        rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
            ENNReal.mul_ne_top h12ne ENNReal.ofReal_ne_top⟩) ENNReal.one_ne_top,
          ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top h12ne ENNReal.ofReal_ne_top),
          ENNReal.toReal_ofReal (pow_nonneg hΛnn 2), ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_one, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hAnn]
        ring
      rwa [e] at h
    have hα2 : ∀ c : Real, 0 < c →
        ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        ≤ K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        + ((1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        + (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) := by
      intro c hc
      have hDdne : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hdU1
      have hDcne : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hdcU1
      have hle : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹
          ≤ ENNReal.ofReal K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + (ENNReal.ofReal (1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + ENNReal.ofReal (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹)) := by
        rw [haUeq]
        exact add_le_add hP1N (hP2N c hc)
      have hRHSne : ENNReal.ofReal K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + (ENNReal.ofReal (1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + ENNReal.ofReal (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹)) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDdne,
          ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbUfin,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDcne⟩⟩
      have h := (ENNReal.toReal_le_toReal haUfin hRHSne).mpr hle
      have e : (ENNReal.ofReal K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + (ENNReal.ofReal (1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹)
          + ENNReal.ofReal (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹))).toReal
          = K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
          + ((1 / (2 * c)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
          + (c / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDdne)
            (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbUfin,
              ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDcne⟩),
          ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbUfin)
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDcne)]
        congr 1
        · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]
        · congr 1
          · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : Real) ≤ 1 / (2 * c))]
          · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : (0 : Real) ≤ c / 2)]
      rwa [e] at h
    have hdU1' : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal ≤ 1 := by
      have h := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hdU1) ENNReal.one_ne_top).mpr hdU1
      rwa [ENNReal.toReal_one] at h
    have hdcEq : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        = 1 - ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := by
      have h2 : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
          + (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
          = ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
          + ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
        ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top hdU1) (ne_top_of_le_ne_top ENNReal.one_ne_top hdcU1)
      rw [hsumN, ENNReal.toReal_one] at h2
      linarith
    -- optimize the AM-GM parameter: α ≤ K * d + sqrt (β * (1 - d))
    have hopt : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        ≤ K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        + Real.sqrt (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
        * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) := by
      by_cases hdc0 : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal = 0
      · by_contra hcon
        push_neg at hcon
        rw [hdc0, mul_zero, Real.sqrt_zero, add_zero] at hcon
        by_cases hβ0 : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal = 0
        · have h := hα2 1 one_pos
          simp only [hβ0, hdc0, mul_zero, add_zero, zero_mul] at h
          linarith
        · have hpos : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
            - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := sub_pos.mpr hcon
          have hβpos : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hβ0)
          have hc : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              / (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) :=
            div_pos hβpos hpos
          have h := hα2 _ hc
          simp only [hdc0, mul_zero, add_zero] at h
          have hceq : (1 / (2 * (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              / (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal))))
              * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              = (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) / 2 := by
            field_simp [hc.ne', hβpos.ne', hpos.ne'] <;> ring
          rw [hceq] at h
          linarith
      · by_cases hβ0 : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal = 0
        · by_contra hcon
          push_neg at hcon
          rw [hβ0, zero_mul, Real.sqrt_zero, add_zero] at hcon
          have hpos : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := sub_pos.mpr hcon
          have hdcpos : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hdc0)
          have hc : 0 < (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal)
              / ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
            div_pos hpos hdcpos
          have h := hα2 _ hc
          simp only [hβ0, mul_zero, zero_add] at h
          have hceq : (((((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal)
              / ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) / 2)
              * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              = (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              - K * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) / 2 := by
            field_simp [hdcpos.ne']
          rw [hceq] at h
          linarith
        · have hβpos : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hβ0)
          have hdcpos : 0 < ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hdc0)
          set c₀ : Real := Real.sqrt (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
            / ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) with hc₀def
          have hc₀ : 0 < c₀ := Real.sqrt_pos.mpr (div_pos hβpos hdcpos)
          have h := hα2 c₀ hc₀
          have hsq : c₀ ^ 2 = ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              / ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal :=
            Real.sq_sqrt (div_nonneg hβpos.le hdcpos.le)
          have hβeq : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              = c₀ ^ 2 * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := by
            rw [hsq]; field_simp [hdcpos.ne']
          have hsqrt : Real.sqrt (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal)
              = c₀ * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := by
            have he : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                = (c₀ * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) ^ 2 := by
              rw [mul_pow, hsq]; field_simp [hdcpos.ne']
            rw [he, Real.sqrt_sq (by positivity : (0 : Real) ≤ c₀
              * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal)]
          have hkey : (1 / (2 * c₀)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              + (c₀ / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              = Real.sqrt (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
              * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) := by
            calc (1 / (2 * c₀)) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                + (c₀ / 2) * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                = (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                + c₀ ^ 2 * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) / (2 * c₀) := by
                  field_simp [hc₀.ne'] <;> ring
            _ = (c₀ ^ 2 * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                + c₀ ^ 2 * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) / (2 * c₀) := by
                  rw [hβeq]
            _ = c₀ * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal := by
                  field_simp [hc₀.ne'] <;> ring
            _ = Real.sqrt (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ^ 2) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal
                * ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if K < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) := hsqrt.symm
          rw [hkey] at h
          exact h
    -- apply the Paley–Zygmund real step D3
    have hfin1 : ((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal ≤ ρ.toReal := by
      refine hM Λ A _ _ _ hΛM hAnn hcase hα1 ?_ hβ ENNReal.toReal_nonneg hdU1'
      rw [← hdcEq]
      refine hopt.trans (add_le_add_left ?_ _)
      have h := mul_le_mul_of_nonneg_left hdU1' hK
      rwa [mul_one] at h
    calc (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
        = ENNReal.ofReal (((∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹).toReal) :=
          (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hdU1)).symm
    _ ≤ ENNReal.ofReal ρ.toReal := ENNReal.ofReal_le_ofReal hfin1
    _ = ρ := ENNReal.ofReal_toReal hρtop
  · -- CASE 2: Λ * sqrt Λ ≤ A. One atom carries mass ≥ A/(2Λ) ≥ sqrt Λ / 2; extract it (D5) and use D4.
    have hsqrt1 : (1 : Real) ≤ Real.sqrt Λ := by
      have h := Real.sqrt_le_sqrt hΛ1
      rwa [Real.sqrt_one] at h
    have hApos : (0 : Real) < A :=
      lt_of_lt_of_le (mul_pos (zero_lt_one.trans_le hΛ1) (zero_lt_one.trans_le hsqrt1)) hcase
    obtain ⟨ys, hyIcc, hymass⟩ := Kyprianou.Ch05.atom_mass_extraction
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi δ hδ hδ1 (A / (2 * Λ)) (by
        rw [← hΛdef, ← hAdef]
        have e : (A / (2 * Λ)) * Λ = A / 2 := by field_simp [hΛpos.ne']
        rw [e]; linarith)
    have hm1 : Real.sqrt Λ / 2 ≤ (Pi {ys}).toReal := by
      have e : (Λ * Real.sqrt Λ) / (2 * Λ) = Real.sqrt Λ / 2 := by field_simp [hΛpos.ne'] <;> ring
      have h2 : (Λ * Real.sqrt Λ) / (2 * Λ) ≤ A / (2 * Λ) :=
        (div_le_div_iff_of_pos_right (by linarith : (0 : Real) < 2 * Λ)).mpr hcase
      rw [← e]
      exact le_trans h2 hymass
    have hmM : M₄ ≤ (Pi {ys}).toReal := by
      by_cases hM4 : M₄ ≤ 0
      · exact hM4.trans ENNReal.toReal_nonneg
      · have hΛ4 : (2 * M₄) ^ 2 ≤ Λ := hT4.trans hΛT
        have hsqrt : 2 * M₄ ≤ Real.sqrt Λ := by
          have h := Real.sqrt_le_sqrt hΛ4
          rwa [Real.sqrt_sq (by linarith : (0 : Real) ≤ 2 * M₄)] at h
        have h3 : M₄ ≤ Real.sqrt Λ / 2 := by linarith
        exact h3.trans hm1
    have hypos : (0 : Real) < ys := hδ.trans_le hyIcc.1
    obtain ⟨U0₄, hU0₄⟩ := hM₄ (Pi {ys}).toReal ys hmM hypos
    have hRge : ∀ u : Real, (Pi {ys}).toReal * (1 - Real.cos (u * ys)) ≤ (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal := by
      intro u
      have hle : Pi {ys} * ENNReal.ofReal (1 - Real.cos (u * ys))
          ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi := by
        calc Pi {ys} * ENNReal.ofReal (1 - Real.cos (u * ys))
            = ∫⁻ y in {ys}, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi := by
              rw [mul_comm]; exact (lintegral_singleton (fun y => ENNReal.ofReal (1 - Real.cos (u * y))) ys).symm
        _ ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi :=
            lintegral_mono_set (Set.singleton_subset_iff.mpr hyIcc)
      have hPiys : Pi {ys} = ENNReal.ofReal (Pi {ys}).toReal :=
        (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin.ne (measure_mono (Set.singleton_subset_iff.mpr hyIcc)))).symm
      have hle2 : ENNReal.ofReal ((Pi {ys}).toReal * (1 - Real.cos (u * ys)))
          ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi := by
        rwa [hPiys, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hle
      have htoR := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hRfin u)).mpr hle2
      rwa [ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (by
        have h := Real.cos_le_one (u * ys); linarith : (0 : Real) ≤ 1 - Real.cos (u * ys)))] at htoR
    have hcomp : ∀ W : Real, (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹
        ≤ (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal (if (Pi {ys}).toReal * (1 - Real.cos (u * ys)) ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal W)⁻¹ := by
      intro W
      apply mul_le_mul _ le_rfl bot_le bot_le
      apply lintegral_mono
      intro u
      by_cases h : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K
      · simp only [if_pos h, if_pos (le_trans (hRge u) h), le_refl]
      · simp only [if_neg h, ENNReal.ofReal_zero]; exact bot_le
    refine ⟨U0₄, fun W hW => (hcomp W).trans (hU0₄ W hW)⟩

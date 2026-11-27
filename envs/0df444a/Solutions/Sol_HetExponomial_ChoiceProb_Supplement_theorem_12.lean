-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:43.480155+00:00
-- url     : https://prove2.me/submissions/edbd8c32-132e-476a-a7a0-fe065a4f5a70

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    -- (a) Products Symmetric in Error Distribution
    ((∃ c : ℝ, ∀ i, lam i = c) →
      ∀ σ : Fin n ≃ Fin n, Monotone (fun s => α (σ s)) →
        (∃ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar) ∧
          ∀ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar →
            (∀ s : Fin n,
                ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
              IsPriceNE α β lam (eqPrices α β ustar) ∧
              (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
              Monotone (fun s => eqPrices α β ustar (σ s)) ∧
              Monotone (fun s => choiceProb (util α β (eqPrices α β ustar)) lam (σ s)) ∧
              Monotone (fun s => firmRevenue α β lam (eqPrices α β ustar) (σ s))) ∧
    -- (b) Products Symmetric in Intrinsic Desirability
    ((∃ a : ℝ, ∀ i, α i = a) →
      ∀ σ : Fin n ≃ Fin n, Antitone (fun s => lam (σ s)) →
        (∃ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar) ∧
          ∀ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar →
            (∀ s : Fin n,
                ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
              IsPriceNE α β lam (eqPrices α β ustar) ∧
              (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
              Antitone (fun s => eqPrices α β ustar (σ s)) ∧
              Antitone (fun s => choiceProb (util α β (eqPrices α β ustar)) lam (σ s)) ∧
              Antitone (fun s => firmRevenue α β lam (eqPrices α β ustar) (σ s))) ∧
    -- (c) Purely Symmetric Products
    (∀ c a : ℝ, (∀ i, lam i = c) → (∀ i, α i = a) →
      IsPriceNE α β lam (fun _ => 1 / (β * c * ((n : ℝ) - 1))) ∧
        (∀ p, IsPriceNE α β lam p → p = fun _ => 1 / (β * c * ((n : ℝ) - 1))) ∧
        ∀ i, choiceProb (util α β (fun _ => 1 / (β * c * ((n : ℝ) - 1)))) lam i = 1 / n ∧
          firmRevenue α β lam (fun _ => 1 / (β * c * ((n : ℝ) - 1))) i =
            1 / (β * c * n * ((n : ℝ) - 1))) := by
              classical
              letI : ∀ j : Fin n, IsProbabilityMeasure (expMeasure (lam j)) :=
                fun j => isProbabilityMeasure_expMeasure (hlam j)
              have htail : ∀ (r : ℝ), 0 < r → ∀ x : ℝ,
                  expMeasure r (Set.Ici x) = ENNReal.ofReal (Real.exp (-(r * max x 0))) := by
                intro r hr x
                letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
                letI : NullSingletonClass (expMeasure r) := by
                  unfold expMeasure gammaMeasure
                  infer_instance
                rw [← measure_congr (Ioi_ae_eq_Ici (μ := expMeasure r) (a := x))]
                rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _)]
                rw [measure_univ, ← ofReal_cdf, cdf_expMeasure_eq hr]
                by_cases hx : 0 ≤ x
                · rw [if_pos hx, max_eq_left hx]
                  have he : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
                  rw [ENNReal.ofReal_sub 1 (Real.exp_pos _).le, ENNReal.ofReal_one,
                    ENNReal.sub_sub_cancel (by simp) (ENNReal.ofReal_le_one.mpr he)]
                · rw [if_neg hx, max_eq_right (le_of_not_ge hx)]
                  simp
              have hslice : ∀ (u : Fin n → ℝ) (i : Fin n),
                  choiceProb u lam i =
                    (∫⁻ z, ∏ j ∈ Finset.univ.erase i,
                      ENNReal.ofReal (Real.exp (-(lam j * max (u j - u i + z) 0)))
                      ∂expMeasure (lam i)).toReal := by
                intro u i
                cases n with
                | zero => omega
                | succ m =>
                  let A : Set (Fin (m+1) → ℝ) :=
                    {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                  have hA : MeasurableSet A := by
                    dsimp [A]
                    measurability
                  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i
                  have he := measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i
                  have hmeas : MeasurableSet (e.symm ⁻¹' A) := e.symm.measurable hA
                  unfold choiceProb errorLaw
                  change ((Measure.pi fun j => expMeasure (lam j)) A).toReal = _
                  rw [← he.symm.measure_preimage hA.nullMeasurableSet, Measure.prod_apply hmeas]
                  congr 1
                  apply lintegral_congr
                  intro z
                  have hs : Prod.mk z ⁻¹' (e.symm ⁻¹' A) =
                      Set.pi Set.univ (fun j : Fin m => Set.Ici (u (i.succAbove j) - u i + z)) := by
                    ext y
                    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici,
                      e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, A,
                      Set.mem_setOf_eq, Equiv.coe_fn_mk]
                    rw [i.forall_iff_succAbove]
                    simp only [Fin.insertNth_apply_same, ne_eq, not_true_eq_false, IsEmpty.forall_iff,
                      implies_true, Fin.succAbove_ne, not_false_eq_true, Fin.insertNth_apply_succAbove,
                      true_implies, true_and]
                    constructor <;> intro h j <;> specialize h j <;> linarith
                  rw [hs, Measure.pi_pi]
                  simp_rw [htail _ (hlam _)]
                  have hp := i.prod_univ_succAbove (fun j => if j = i then (1 : ENNReal) else
                    ENNReal.ofReal (Real.exp (-(lam j * max (u j - u i + z) 0))))
                  simpa [Finset.prod_ite, Finset.filter_ne'] using hp.symm
              let E : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i z =>
                Real.exp (-(∑ j ∈ Finset.univ.erase i, lam j * max (u j - u i + z) 0))
              have hEcont : ∀ u i, Continuous (E u i) := by
                intro u i
                dsimp [E]
                fun_prop
              have hreal : ∀ u i, choiceProb u lam i = ∫ z, E u i z ∂expMeasure (lam i) := by
                intro u i
                rw [integral_eq_lintegral_of_nonneg_ae
                  (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
                  (hEcont u i).aestronglyMeasurable, hslice]
                congr 1
                apply lintegral_congr
                intro z
                rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
                rw [← Real.exp_sum, Finset.sum_neg_distrib]
              have hdensity : ∀ u i, choiceProb u lam i =
                  ∫ z in Set.Ici (0 : ℝ), lam i * Real.exp (-(lam i * z)) * E u i z := by
                intro u i
                rw [hreal, expMeasure, gammaMeasure,
                  integral_withDensity_eq_integral_toReal_smul]
                · rw [← integral_indicator measurableSet_Ici]
                  apply integral_congr_ae
                  filter_upwards [] with z
                  simp only [gammaPDF, gammaPDFReal, Real.rpow_one, Real.Gamma_one, div_one,
                    sub_self, Real.rpow_zero, mul_one, smul_eq_mul]
                  by_cases hz : 0 ≤ z
                  · simp [hz, ENNReal.toReal_ofReal, (mul_pos (hlam i) (Real.exp_pos _)).le]
                  · simp [hz]
                · exact (measurable_gammaPDFReal 1 (lam i)).ennreal_ofReal
                · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
              have hchange : ∀ (f : ℝ → ℝ) (x : ℝ),
                  (∫ z in Set.Ici (0 : ℝ), f (x - z)) = ∫ t in Set.Iic x, f t := by
                intro f x
                have h := (volume.measurePreserving_sub_left x).setIntegral_preimage_emb
                  (MeasurableEquiv.subLeft x).measurableEmbedding f (Set.Iic x)
                have hs : (fun t : ℝ => x - t) ⁻¹' Set.Iic x = Set.Ici 0 := by
                  ext z
                  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
                  constructor <;> intro hz <;> linarith
                simpa only [hs] using h
              let D : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i t =>
                Real.exp (lam i * t - ∑ j ∈ Finset.univ.erase i, lam j * max (u j - t) 0)
              have hDcont : ∀ u i, Continuous (D u i) := by
                intro u i
                dsimp [D]
                fun_prop
              have hDint : ∀ u i x, IntegrableOn (D u i) (Set.Iic x) := by
                intro u i x
                refine (integrableOn_exp_mul_Iic (hlam i) x).mono'
                  (hDcont u i).aestronglyMeasurable ?_
                filter_upwards [] with t
                rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                apply Real.exp_le_exp.mpr
                have hsum : 0 ≤ ∑ j ∈ Finset.univ.erase i, lam j * max (u j - t) 0 :=
                  Finset.sum_nonneg fun j _ => mul_nonneg (hlam j).le (le_max_right _ _)
                linarith
              have hprimitive : ∀ u i x, choiceProb (Function.update u i x) lam i =
                  lam i * Real.exp (-(lam i * x)) * ∫ t in Set.Iic x, D u i t := by
                intro u i x
                rw [hdensity, ← hchange (D u i) x, ← integral_const_mul]
                apply setIntegral_congr_fun measurableSet_Ici
                intro z _
                have hs : (∑ j ∈ Finset.univ.erase i,
                      lam j * max ((Function.update u i x) j - (Function.update u i x) i + z) 0) =
                    ∑ j ∈ Finset.univ.erase i, lam j * max (u j - (x - z)) 0 := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [Function.update_self, Function.update_of_ne (Finset.mem_erase.mp hj).1]
                  congr 2
                  ring
                dsimp [E, D]
                rw [hs]
                simp only [mul_assoc, ← Real.exp_add]
                congr 2
                ring
              have hprimDeriv : ∀ u i x,
                  HasDerivAt (fun x => ∫ t in Set.Iic x, D u i t) (D u i x) x := by
                intro u i x
                have hd := intervalIntegral.integral_hasDerivAt_right
                  ((hDcont u i).intervalIntegrable x x) (hDcont u i).stronglyMeasurable.stronglyMeasurableAtFilter
                  (hDcont u i).continuousAt
                have hfun : (fun y => ∫ t in Set.Iic y, D u i t) =
                    fun y => (∫ t in x..y, D u i t) + ∫ t in Set.Iic x, D u i t := by
                  funext y
                  rw [← intervalIntegral.integral_Iic_sub_Iic (hDint u i x) (hDint u i y)]
                  ring
                rw [hfun]
                exact hd.add_const _
              let H : (Fin n → ℝ) → Fin n → ℝ := fun u i =>
                Real.exp (-(∑ j ∈ Finset.univ.erase i, lam j * max (u j - u i) 0))
              have hderiv : ∀ u i x,
                  HasDerivAt (fun x => choiceProb (Function.update u i x) lam i)
                    (lam i * (H (Function.update u i x) i - choiceProb (Function.update u i x) lam i)) x := by
                intro u i x
                have hd := ((((hasDerivAt_id x).const_mul (lam i)).neg.exp).const_mul (lam i)).mul
                  (hprimDeriv u i x)
                convert! hd using 1
                · funext y
                  exact hprimitive u i y
                · rw [hprimitive]
                  have hs : H (Function.update u i x) i =
                      Real.exp (-(∑ j ∈ Finset.univ.erase i, lam j * max (u j - x) 0)) := by
                    dsimp [H]
                    congr 2
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Function.update_self, Function.update_of_ne (Finset.mem_erase.mp hj).1]
                  rw [hs]
                  dsimp [D]
                  have he : Real.exp (-(lam i * x)) *
                      Real.exp (lam i * x - ∑ j ∈ Finset.univ.erase i, lam j * max (u j - x) 0) =
                      Real.exp (-(∑ j ∈ Finset.univ.erase i, lam j * max (u j - x) 0)) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
                  linear_combination -(lam i) * he
              have hpartial : ∀ u i,
                  partialU (fun v => choiceProb v lam i) i u = lam i * (H u i - choiceProb u lam i) := by
                intro u i
                simpa [partialU] using (hderiv u i (u i)).deriv
              have hmaxdiff : ∀ a z : ℝ, 0 ≤ z → 0 ≤ max (a + z) 0 - max a 0 := by
                intro a z hz
                exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)
              let N : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i z =>
                Real.exp (-(lam i * z + ∑ j ∈ Finset.univ.erase i,
                  lam j * (max (u j - u i + z) 0 - max (u j - u i) 0)))
              let K : (Fin n → ℝ) → Fin n → ℝ := fun u i => ∫ z in Set.Ici (0 : ℝ), N u i z
              have hNcont : ∀ u i, Continuous (N u i) := by
                intro u i
                dsimp [N]
                fun_prop
              have hNbound : ∀ u i z, 0 ≤ z → N u i z ≤ Real.exp (-(lam i * z)) := by
                intro u i z hz
                apply Real.exp_le_exp.mpr
                have hs : 0 ≤ ∑ j ∈ Finset.univ.erase i,
                    lam j * (max (u j - u i + z) 0 - max (u j - u i) 0) :=
                  Finset.sum_nonneg fun j _ => mul_nonneg (hlam j).le (hmaxdiff _ _ hz)
                linarith
              have hexpint : ∀ i, IntegrableOn (fun z => Real.exp (-(lam i * z))) (Set.Ici (0 : ℝ)) := by
                intro i
                rw [integrableOn_Ici_iff_integrableOn_Ioi]
                simpa only [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos (hlam i)) 0
              have hNint : ∀ u i, IntegrableOn (N u i) (Set.Ici (0 : ℝ)) := by
                intro u i
                refine (hexpint i).mono' (hNcont u i).aestronglyMeasurable ?_
                filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
                rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                exact hNbound u i z hz
              have hKbridge : ∀ u i, choiceProb u lam i = lam i * H u i * K u i := by
                intro u i
                rw [hdensity]
                dsimp [K]
                rw [← integral_const_mul]
                apply setIntegral_congr_fun measurableSet_Ici
                intro z _
                dsimp [N, E, H]
                simp only [mul_assoc, ← Real.exp_add]
                congr 2
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
                ring
              have hKpos : ∀ u i, 0 < K u i := by
                intro u i
                apply (integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) (hNint u i)).mpr
                have hs : Function.support (N u i) = Set.univ := by
                  ext z
                  simp [N, Function.mem_support, Real.exp_ne_zero]
                change 0 < (volume.restrict (Set.Ici 0)) (Function.support (N u i))
                rw [hs]
                simp
              have hKlt : ∀ u i, K u i < 1 / lam i := by
                intro u i
                obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i := by
                  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
                  exact exists_ne i
                let z₀ : ℝ := max (u i - u j) 0 + 1
                have hz₀ : 0 < z₀ := by dsimp [z₀]; linarith [le_max_right (u i - u j) 0]
                have hstrict : N u i z₀ < Real.exp (-(lam i * z₀)) := by
                  apply Real.exp_lt_exp.mpr
                  have hj : 0 < lam j * (max (u j - u i + z₀) 0 - max (u j - u i) 0) := by
                    apply mul_pos (hlam j)
                    dsimp [z₀]
                    by_cases h : 0 ≤ u j - u i
                    · rw [max_eq_left h, max_eq_left (by linarith [le_max_right (u i - u j) 0])]
                      linarith [le_max_right (u i - u j) 0]
                    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith [le_max_left (u i - u j) 0])]
                      linarith [le_max_left (u i - u j) 0]
                  have hs := Finset.single_le_sum
                    (fun k (_ : k ∈ Finset.univ.erase i) =>
                      mul_nonneg (hlam k).le (hmaxdiff (u k - u i) z₀ hz₀.le))
                    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
                  linarith
                let g : ℝ → ℝ := fun z => Real.exp (-(lam i * z)) - N u i z
                have hgint : IntegrableOn g (Set.Ici (0 : ℝ)) := (hexpint i).sub (hNint u i)
                have hg : 0 < ∫ z in Set.Ici (0 : ℝ), g z := by
                  apply (integral_pos_iff_support_of_nonneg_ae
                    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
                        exact sub_nonneg.mpr (hNbound u i z hz)) hgint).mpr
                  let S : Set ℝ := {z | 0 < z ∧ N u i z < Real.exp (-(lam i * z))}
                  have hS : IsOpen S := isOpen_lt continuous_const continuous_id |>.inter
                    (isOpen_lt (hNcont u i) (by fun_prop))
                  have hvol : 0 < volume S := hS.measure_pos volume ⟨z₀, hz₀, hstrict⟩
                  have hsub : S ⊆ Function.support g ∩ Set.Ici 0 := by
                    intro z hz
                    exact ⟨by dsimp [Function.support, g]; linarith [hz.2], hz.1.le⟩
                  rw [Measure.restrict_apply (by
                    exact (by fun_prop : Continuous g).isOpen_support.measurableSet)]
                  exact hvol.trans_le (measure_mono hsub)
                have he : (∫ z in Set.Ici (0 : ℝ), Real.exp (-(lam i * z))) = 1 / lam i := by
                  rw [integral_Ici_eq_integral_Ioi]
                  simpa using integral_exp_mul_Ioi (neg_neg_of_pos (hlam i)) 0
                rw [integral_sub (hexpint i) (hNint u i), he] at hg
                exact sub_pos.mp hg
              have htau : ∀ u i, tau u lam i = K u i / (1 - lam i * K u i) := by
                intro u i
                rw [tau, hpartial, hKbridge]
                have hp : 0 < H u i := Real.exp_pos _
                have hk : 0 < 1 - lam i * K u i := by
                  have h := (lt_div_iff₀ (hlam i)).mp (hKlt u i)
                  nlinarith only [h]
                field_simp [ne_of_gt (hlam i), ne_of_gt hp, ne_of_gt hk]
                <;> ring
              have hKden : ∀ u i, 0 < 1 - lam i * K u i := by
                intro u i
                have h := (lt_div_iff₀ (hlam i)).mp (hKlt u i)
                nlinarith only [h]
              have htaupos : ∀ u i, 0 < tau u lam i := by
                intro u i
                rw [htau]
                exact div_pos (hKpos u i) (hKden u i)
              have hQpos : ∀ u i, 0 < choiceProb u lam i := by
                intro u i
                rw [hKbridge]
                exact mul_pos (mul_pos (hlam i) (Real.exp_pos _)) (hKpos u i)
              have hderivpos : ∀ u i, 0 < lam i * (H u i - choiceProb u lam i) := by
                intro u i
                rw [hKbridge]
                have hp : 0 < H u i := Real.exp_pos _
                have hk := hKden u i
                nlinarith only [mul_pos hp hk, hlam i]
              have hmaxmono : ∀ a b z : ℝ, a ≤ b → 0 ≤ z →
                  max (a + z) 0 - max a 0 ≤ max (b + z) 0 - max b 0 := by
                intro a b z hab hz
                simp only [max_def]
                split_ifs <;> linarith
              have hNall : ∀ u i z, 0 ≤ z → N u i z =
                  Real.exp (-(∑ j, lam j * (max (u j - u i + z) 0 - max (u j - u i) 0))) := by
                intro u i z hz
                dsimp [N]
                congr 2
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
                simp only [sub_self, zero_add, max_self, sub_zero, max_eq_left hz]
                ring
              have hKorder : ∀ u v i j,
                  (∀ k, u k - u i ≤ v k - v j) → K v j ≤ K u i := by
                intro u v i j h
                apply integral_mono_ae (hNint v j) (hNint u i)
                filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
                rw [hNall _ _ _ hz, hNall _ _ _ hz]
                apply Real.exp_le_exp.mpr
                exact neg_le_neg (Finset.sum_le_sum fun k _ =>
                  mul_le_mul_of_nonneg_left (hmaxmono _ _ _ (h k) hz) (hlam k).le)
              have htauorder : ∀ u v i j, K u i ≤ K v j → lam i ≤ lam j →
                  tau u lam i ≤ tau v lam j := by
                intro u v i j hk hl
                rw [htau, htau, div_le_div_iff₀ (hKden u i) (hKden v j)]
                have hprod := mul_nonneg (sub_nonneg.mpr hl) (mul_nonneg (hKpos u i).le (hKpos v j).le)
                nlinarith only [hk, hprod]
              have htaugap : ∀ u v i, (∀ j, u j - u i ≤ v j - v i) →
                  tau v lam i ≤ tau u lam i := by
                intro u v i h
                exact htauorder v u i i (hKorder u v i i h) le_rfl
              have htauownmono : ∀ u i, Monotone (fun x => tau (Function.update u i x) lam i) := by
                intro u i x y hxy
                apply htaugap
                intro j
                by_cases hji : j = i
                · subst j; simp
                · simp only [Function.update_self, Function.update_of_ne hji]
                  linarith
              have htauowncont : ∀ u i, Continuous (fun x => tau (Function.update u i x) lam i) := by
                intro u i
                unfold tau
                apply Continuous.div
                · exact continuous_iff_continuousAt.mpr fun x => (hderiv u i x).continuousAt
                · have heq : (fun x => partialU (fun v => choiceProb v lam i) i (Function.update u i x)) =
                      fun x => lam i * (H (Function.update u i x) i - choiceProb (Function.update u i x) lam i) := by
                    funext x
                    exact hpartial _ _
                  rw [heq]
                  apply continuous_const.mul
                  apply Continuous.sub
                  · dsimp [H]
                    fun_prop
                  · exact continuous_iff_continuousAt.mpr fun x => (hderiv u i x).continuousAt
                · intro x
                  rw [hpartial]
                  exact ne_of_gt (hderivpos _ _)
              let L : ℝ := ∑ j, lam j
              have hLminus : ∀ i, 0 < L - lam i := by
                intro i
                rw [show L - lam i = ∑ j ∈ Finset.univ.erase i, lam j by
                  dsimp [L]; rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]]
                apply Finset.sum_pos
                · intro j _; exact hlam j
                · obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i := by
                    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
                    exact exists_ne i
                  exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩⟩
              have hLpos : 0 < L := by
                have hi := hlam ⟨0, by omega⟩
                have h := hLminus ⟨0, by omega⟩
                linarith
              have hKlow : ∀ u i, (∀ j, u i ≤ u j) → K u i = 1 / L := by
                intro u i h
                change (∫ z in Set.Ici (0 : ℝ), N u i z) = _
                calc
                  _ = ∫ z in Set.Ici (0 : ℝ), Real.exp (-(L * z)) := by
                    apply setIntegral_congr_fun measurableSet_Ici
                    intro z hz
                    change 0 ≤ z at hz
                    rw [hNall _ _ _ hz]
                    congr 2
                    calc
                      _ = ∑ j, lam j * z := by
                        apply Finset.sum_congr rfl
                        intro j _
                        rw [max_eq_left (by linarith [h j]), max_eq_left (sub_nonneg.mpr (h j))]
                        ring
                      _ = _ := by rw [← Finset.sum_mul]
                  _ = 1 / L := by
                    rw [integral_Ici_eq_integral_Ioi]
                    simpa using integral_exp_mul_Ioi (neg_neg_of_pos hLpos) 0
              have htaulow : ∀ u i, (∀ j, u i ≤ u j) → tau u lam i = 1 / (L - lam i) := by
                intro u i h
                rw [htau, hKlow u i h]
                field_simp
                <;> ring
              have htautie : ∀ u i j, u i = u j → lam i ≤ lam j → tau u lam i ≤ tau u lam j := by
                intro u i j hu hl
                apply htauorder _ _ _ _ _ hl
                apply hKorder
                intro k
                rw [hu]
              have htauindep : ∀ u v i, v i = u i →
                  (∀ j, u j < u i → v j = u j) →
                  (∀ j, u i ≤ u j → u i ≤ v j) → tau v lam i = tau u lam i := by
                intro u v i hi hlo hhi
                suffices hk : K v i = K u i by rw [htau, htau, hk]
                apply setIntegral_congr_fun measurableSet_Ici
                intro z hz
                change 0 ≤ z at hz
                rw [hNall _ _ _ hz, hNall _ _ _ hz]
                congr 2
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : u j < u i
                · rw [hlo j hj, hi]
                · have huj := le_of_not_gt hj
                  have hvj := hhi j huj
                  rw [hi, max_eq_left (by linarith), max_eq_left (sub_nonneg.mpr hvj),
                    max_eq_left (by linarith), max_eq_left (sub_nonneg.mpr huj)]
                  ring
              have hroot : ∀ (u : Fin n → ℝ) (i : Fin n) (a : ℝ),
                  ∃! x : ℝ, a - x = tau (Function.update u i x) lam i := by
                intro u i a
                obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ u ⟨i, Finset.mem_univ i⟩
                let b := min (a - 1 / (L - lam i)) (u j)
                have hba : b ≤ a := by
                  have hp := one_div_pos.mpr (hLminus i)
                  have hb := min_le_left (a - 1 / (L - lam i)) (u j)
                  dsimp [b]
                  linarith
                have hb : ∀ k, b ≤ u k := by
                  intro k
                  exact (min_le_right _ _).trans (hj k (Finset.mem_univ k))
                let f : ℝ → ℝ := fun x => a - x - tau (Function.update u i x) lam i
                have hf : Continuous f := (continuous_const.sub continuous_id).sub (htauowncont u i)
                have hfb : 0 ≤ f b := by
                  have ht : tau (Function.update u i b) lam i = 1 / (L - lam i) := by
                    apply htaulow
                    intro k
                    by_cases hki : k = i
                    · subst k; exact le_rfl
                    · simp only [Function.update_self, Function.update_of_ne hki]
                      exact hb k
                  dsimp [f]
                  rw [ht]
                  have hh := min_le_left (a - 1 / (L - lam i)) (u j)
                  dsimp [b]
                  linarith
                have hfa : f a ≤ 0 := by
                  dsimp [f]
                  linarith [htaupos (Function.update u i a) i]
                obtain ⟨x, _, hx⟩ := intermediate_value_Icc' hba hf.continuousOn ⟨hfa, hfb⟩
                have hx' : a - x = tau (Function.update u i x) lam i := by
                  dsimp [f] at hx
                  linarith
                refine ⟨x, hx', ?_⟩
                intro y hy
                have hanti : StrictAnti f := by
                  intro v w hvw
                  have ht := htauownmono u i hvw.le
                  dsimp [f]
                  linarith
                apply hanti.injective
                dsimp [f]
                linarith
              have hcondcongr : ∀ S u v i x, (∀ j ∈ S, u j = v j) →
                  tauCond α lam S u i x = tauCond α lam S v i x := by
                intro S u v i x h
                unfold tauCond
                congr 1
                funext j
                dsimp [condVec]
                split_ifs with hji hjS
                · rfl
                · exact h j hjS
                · rfl
              have hcondroot : ∀ S u i, ∃! x : ℝ, α i - x = tauCond α lam S u i x := by
                intro S u i
                have he : ∀ x, condVec α S u i x = Function.update (condVec α S u i 0) i x := by
                  intro x
                  funext j
                  by_cases hji : j = i <;> simp [condVec, Function.update_apply, hji]
                obtain ⟨x, hx, hu⟩ := hroot (condVec α S u i 0) i (α i)
                refine ⟨x, ?_, ?_⟩
                · change α i - x = tau (condVec α S u i x) lam i
                  rw [he]
                  exact hx
                · intro y hy
                  apply hu
                  change α i - y = tau (condVec α S u i y) lam i at hy
                  rwa [he] at hy
              have hutilupdate : ∀ p i q, util α β (Function.update p i q) =
                  Function.update (util α β p) i (α i - β * q) := by
                intro p i q
                funext j
                by_cases hji : j = i <;> simp [util, Function.update_apply, hji]
              have hpriceDeriv : ∀ p i q,
                  HasDerivAt (fun q => firmRevenue α β lam (Function.update p i q) i)
                    (lam i * (H (util α β (Function.update p i q)) i -
                      choiceProb (util α β (Function.update p i q)) lam i) *
                      (tau (util α β (Function.update p i q)) lam i - β * q)) q := by
                intro p i q
                have hd := (hasDerivAt_id q).mul
                  ((hderiv (util α β p) i (α i - β * q)).comp q
                    ((hasDerivAt_const q (α i)).sub ((hasDerivAt_id q).const_mul β)))
                convert! hd using 1
                · funext x
                  simp [firmRevenue, hutilupdate]
                · rw [tau, hpartial, hutilupdate]
                  have hp := ne_of_gt (hderivpos (Function.update (util α β p) i (α i - β * q)) i)
                  rw [mul_sub]
                  rw [mul_comm _ (choiceProb (Function.update (util α β p) i (α i - β * q)) lam i / _),
                    div_mul_cancel₀ _ hp]
                  dsimp
                  ring
              have hNEiff : ∀ p, IsPriceNE α β lam p ↔
                  ∀ i, β * p i = tau (util α β p) lam i := by
                intro p
                constructor
                · intro hp i
                  have hpi : 0 < p i := by
                    by_contra hh
                    have hzero : p i = 0 := le_antisymm (le_of_not_gt hh) (hp.1 i)
                    have h := hp.2 i 1 zero_le_one
                    have hpos := hQpos (util α β (Function.update p i 1)) i
                    have hh : choiceProb (util α β (Function.update p i 1)) lam i ≤ 0 := by
                      simpa [firmRevenue, hzero] using h
                    exact not_le_of_gt hpos hh
                  have hm : IsLocalMax (fun q => firmRevenue α β lam (Function.update p i q) i) (p i) := by
                    apply IsMaxOn.isLocalMax (s := Set.Ici 0)
                    · intro q hq
                      simpa using hp.2 i q hq
                    · exact Ici_mem_nhds hpi
                  have hz := hm.hasDerivAt_eq_zero (hpriceDeriv p i (p i))
                  simp only [Function.update_eq_self] at hz
                  have hpos := hderivpos (util α β p) i
                  rcases mul_eq_zero.mp hz with h | h
                  · exact False.elim (ne_of_gt hpos h)
                  · linarith
                · intro hp
                  have hpi : ∀ i, 0 < p i := by
                    intro i
                    have hh := htaupos (util α β p) i
                    rw [← hp i] at hh
                    nlinarith only [hh, hβ]
                  refine ⟨fun i => (hpi i).le, ?_⟩
                  intro i q _
                  have hm : IsMaxOn (fun q => firmRevenue α β lam (Function.update p i q) i) Set.univ (p i) := by
                    apply isMaxOn_univ_of_deriv (hpriceDeriv p i (p i)).continuousAt
                      (fun x _ => (hpriceDeriv p i x).differentiableAt.differentiableWithinAt)
                      (fun x _ => (hpriceDeriv p i x).differentiableAt.differentiableWithinAt)
                    · intro x hx
                      change x < p i at hx
                      rw [(hpriceDeriv p i x).deriv]
                      apply mul_nonneg (hderivpos _ _).le
                      have ht := htauownmono (util α β p) i
                        (show α i - β * p i ≤ α i - β * x by nlinarith only [hβ, hx])
                      simp only [show α i - β * p i = (util α β p) i from rfl,
                        Function.update_eq_self] at ht
                      rw [← hutilupdate, ← hp i] at ht
                      nlinarith only [ht, hβ, hx]
                    · intro x hx
                      change p i < x at hx
                      rw [(hpriceDeriv p i x).deriv]
                      apply mul_nonpos_of_nonneg_of_nonpos (hderivpos _ _).le
                      have ht := htauownmono (util α β p) i
                        (show α i - β * x ≤ α i - β * p i by nlinarith only [hβ, hx])
                      simp only [show α i - β * p i = (util α β p) i from rfl,
                        Function.update_eq_self] at ht
                      rw [← hutilupdate, ← hp i] at ht
                      nlinarith only [ht, hβ, hx]
                  simpa using hm (Set.mem_univ q)
              have hNEuniq : ∀ p q, IsPriceNE α β lam p → IsPriceNE α β lam q → p = q := by
                have hle : ∀ p q, IsPriceNE α β lam p → IsPriceNE α β lam q → p ≤ q := by
                  intro p q hp hq
                  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun i => p i - q i)
                    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
                  have ht := htaugap (util α β q) (util α β p) k (by
                    intro j
                    have h := hk j (Finset.mem_univ j)
                    dsimp [util]
                    nlinarith only [h, hβ])
                  rw [← (hNEiff p).mp hp k, ← (hNEiff q).mp hq k] at ht
                  have hk' : p k ≤ q k := (mul_le_mul_iff_right₀ hβ).mp (by simpa [mul_comm] using ht)
                  intro j
                  have h := hk j (Finset.mem_univ j)
                  linarith
                intro p q hp hq
                exact le_antisymm (hle p q hp hq) (hle q p hq hp)
              have hbefore : ∀ (σ : Fin n ≃ Fin n) t j,
                  j ∈ solvedBefore σ t ↔ (σ.symm j).val < t := by
                intro σ t j
                constructor
                · intro h
                  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
                  simpa using hk
                · intro h
                  apply Finset.mem_image.mpr
                  exact ⟨σ.symm j, by simpa using h, by simp⟩
              have hseqExists : ∀ σ : Fin n ≃ Fin n, ∃ u, IsSequentialFOC α lam σ u := by
                intro σ
                have hprefix : ∀ t : ℕ, t ≤ n → ∃ u : Fin n → ℝ,
                    ∀ s : Fin n, s.val < t → α (σ s) - u (σ s) =
                      tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) := by
                  intro t
                  induction t with
                  | zero =>
                    intro _
                    refine ⟨fun _ => 0, ?_⟩
                    intro s hs
                    omega
                  | succ t ih =>
                    intro ht
                    obtain ⟨u, hu⟩ := ih (by omega)
                    let s : Fin n := ⟨t, by omega⟩
                    obtain ⟨x, hx, _⟩ := hcondroot (solvedBefore σ t) u (σ s)
                    refine ⟨Function.update u (σ s) x, ?_⟩
                    intro r hr
                    by_cases hrs : r = s
                    · subst r
                      rw [Function.update_self]
                      change α (σ s) - x = tauCond α lam (solvedBefore σ t)
                        (Function.update u (σ s) x) (σ s) x
                      rw [← hcondcongr (solvedBefore σ t) u (Function.update u (σ s) x) (σ s) x]
                      · exact hx
                      · intro j hj
                        have hne : j ≠ σ s := by
                          intro he
                          rw [he, hbefore] at hj
                          simp [s] at hj
                        simp [Function.update_of_ne hne]
                    · have hr' : r.val < t := by
                        have hnval : r.val ≠ t := by intro h; exact hrs (Fin.ext h)
                        omega
                      have hir : σ r ≠ σ s := fun h => hrs (σ.injective h)
                      rw [Function.update_of_ne hir]
                      rw [← hcondcongr (solvedBefore σ r.val) u (Function.update u (σ s) x) (σ r) (u (σ r))]
                      · exact hu r hr'
                      · intro j hj
                        have hne : j ≠ σ s := by
                          intro he
                          rw [he, hbefore] at hj
                          simp only [Equiv.symm_apply_apply] at hj
                          dsimp [s] at hj
                          omega
                        simp [Function.update_of_ne hne]
                obtain ⟨u, hu⟩ := hprefix n le_rfl
                exact ⟨u, fun s => hu s s.isLt⟩
              have hmaxα : ∀ i, α i ≤ maxAlpha α := by
                intro i
                exact le_ciSup (Finite.bddAbove_range α) i
              have hseqBound : ∀ σ u, IsSequentialFOC α lam σ u → ∀ s, u (σ s) < α (σ s) := by
                intro σ u hu s
                have hp := htaupos (condVec α (solvedBefore σ s.val) u (σ s) (u (σ s))) (σ s)
                have hs := hu s
                change α (σ s) - u (σ s) = tau _ lam (σ s) at hs
                linarith
              have hcondmono : ∀ S u i, Monotone (fun x => tauCond α lam S u i x) := by
                intro S u i x y hxy
                apply htaugap
                intro j
                by_cases hji : j = i
                · subst j; simp
                · simp only [condVec, if_pos rfl, if_neg hji]
                  split_ifs <;> linarith
              have hnextcond : ∀ (σ : Fin n ≃ Fin n) u (s t : Fin n),
                  t.val = s.val + 1 → u (σ s) ≤ maxAlpha α → lam (σ t) ≤ lam (σ s) →
                  tauCond α lam (solvedBefore σ t.val) u (σ t) (u (σ s)) ≤
                    tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) := by
                intro σ u s t hst hb hl
                have hne : s ≠ t := by intro h; subst t; omega
                apply htauorder _ _ _ _ _ hl
                apply le_of_eq
                apply setIntegral_congr_fun measurableSet_Ici
                intro z hz
                change 0 ≤ z at hz
                rw [hNall _ _ _ hz, hNall _ _ _ hz]
                simp only [condVec, if_pos rfl]
                congr 2
                apply Finset.sum_congr rfl
                intro k _
                obtain ⟨r, rfl⟩ := σ.surjective k
                by_cases hrs : r = s
                · subst r
                  simp [hne, hbefore, show s.val < t.val by omega]
                · by_cases hrt : r = t
                  · subst r
                    have hts : ¬t.val < s.val := by omega
                    simp only [Equiv.apply_eq_iff_eq, hbefore, Equiv.symm_apply_apply,
                      if_pos rfl, if_neg (Ne.symm hne), if_neg hts, ite_true, ite_false,
                      lt_self_iff_false, sub_self, zero_add, max_self, sub_zero, max_eq_left hz]
                    rw [max_eq_left (by linarith), max_eq_left (sub_nonneg.mpr hb)]
                    simp
                  · have hval : r.val ≠ s.val := fun h => hrs (Fin.ext h)
                    have hiff : r.val < t.val ↔ r.val < s.val := by omega
                    simp only [Equiv.apply_eq_iff_eq, if_neg hrs, if_neg hrt, hbefore,
                      Equiv.symm_apply_apply, hiff, ite_true]
              have hseqMono : ∀ (σ : Fin n ≃ Fin n), Monotone (fun s => α (σ s)) →
                  Antitone (fun s => lam (σ s)) → ∀ u, IsSequentialFOC α lam σ u →
                  Monotone (fun s => u (σ s)) := by
                intro σ ha hl u hu
                have hadj : ∀ s t : Fin n, t.val = s.val + 1 → u (σ s) ≤ u (σ t) := by
                  intro s t hst
                  have hle : s ≤ t := by exact Fin.le_iff_val_le_val.mpr (by omega)
                  have hb : u (σ s) ≤ maxAlpha α := (hseqBound σ u hu s).le.trans (hmaxα _)
                  have ht := hnextcond σ u s t hst hb (hl hle)
                  by_contra h
                  have hlt := lt_of_not_ge h
                  have hm := hcondmono (solvedBefore σ t.val) u (σ t) hlt.le
                  have hs := hu s
                  have ht' := hu t
                  have ha' := ha hle
                  linarith
                intro s t hst
                have hAux : ∀ m : ℕ, ∀ t : Fin n, t.val = m → s ≤ t → u (σ s) ≤ u (σ t) := by
                  intro m
                  induction m with
                  | zero =>
                    intro t ht hst
                    have he : s = t := Fin.ext (by have hs := Fin.le_iff_val_le_val.mp hst; omega)
                    subst t
                    exact le_rfl
                  | succ m ih =>
                    intro t ht hst
                    by_cases he : s = t
                    · subst t; exact le_rfl
                    · let r : Fin n := ⟨m, by omega⟩
                      have hsval : s.val ≠ t.val := fun h => he (Fin.ext h)
                      have hsr : s ≤ r := Fin.le_iff_val_le_val.mpr (by have hs := Fin.le_iff_val_le_val.mp hst; dsimp [r]; omega)
                      exact (ih r rfl hsr).trans (hadj r t (by dsimp [r]; omega))
                exact hAux t.val t rfl hst
              have hseqFOC : ∀ (σ : Fin n ≃ Fin n) u, IsSequentialFOC α lam σ u →
                  Monotone (fun s => u (σ s)) → ∀ i, α i - u i = tau u lam i := by
                intro σ u hu hm i
                obtain ⟨s, rfl⟩ := σ.surjective i
                have hb : u (σ s) ≤ maxAlpha α := (hseqBound σ u hu s).le.trans (hmaxα _)
                rw [hu s]
                apply Eq.symm
                apply htauindep (condVec α (solvedBefore σ s.val) u (σ s) (u (σ s))) u (σ s)
                · simp [condVec]
                · intro j hj
                  by_cases hji : j = σ s
                  · subst j; simp [condVec]
                  · by_cases hjS : j ∈ solvedBefore σ s.val
                    · simp [condVec, hji, hjS]
                    · simp [condVec, hji, hjS] at hj
                      linarith
                · intro j hj
                  by_cases hji : j = σ s
                  · subst j; simp [condVec]
                  · by_cases hjS : j ∈ solvedBefore σ s.val
                    · simpa [condVec, hji, hjS] using hj
                    · obtain ⟨r, rfl⟩ := σ.surjective j
                      have hsr : s ≤ r := by
                        rw [hbefore] at hjS
                        simp only [Equiv.symm_apply_apply] at hjS
                        exact Fin.le_iff_val_le_val.mpr (by omega)
                      simpa [condVec] using hm hsr
              have hpricesUtil : ∀ u, util α β (eqPrices α β u) = u := by
                intro u
                funext i
                dsimp [util, eqPrices]
                field_simp
                <;> ring
              have hseqNE : ∀ (σ : Fin n ≃ Fin n), Monotone (fun s => α (σ s)) →
                  Antitone (fun s => lam (σ s)) → ∀ u, IsSequentialFOC α lam σ u →
                  IsPriceNE α β lam (eqPrices α β u) := by
                intro σ ha hl u hu
                apply (hNEiff _).mpr
                rw [hpricesUtil]
                intro i
                rw [← hseqFOC σ u hu (hseqMono σ ha hl u hu) i]
                dsimp [eqPrices]
                field_simp
              let F : (Fin n → ℝ) → ℝ → ℝ := fun u t => Real.exp (-(∑ j, lam j * max (u j - t) 0))
              have hFcont : ∀ u, Continuous (F u) := by
                intro u
                dsimp [F]
                fun_prop
              have hFmono : ∀ u, Monotone (F u) := by
                intro u x y hxy
                apply Real.exp_le_exp.mpr
                apply neg_le_neg
                apply Finset.sum_le_sum
                intro j _
                exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (hlam j).le
              have hHF : ∀ u i, H u i = F u (u i) := by
                intro u i
                dsimp [H, F]
                congr 2
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
                simp
              have hFint : ∀ u b, IntegrableOn (F u) (Set.Iic b) := by
                intro u b
                let i : Fin n := ⟨0, by omega⟩
                refine ((integrableOn_exp_mul_Iic (hlam i) b).const_mul (Real.exp (-(lam i * u i)))).mono'
                  (hFcont u).aestronglyMeasurable ?_
                filter_upwards [] with t
                rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
                apply Real.exp_le_exp.mpr
                have hs := Finset.single_le_sum
                  (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hlam j).le (le_max_right (u j - t) 0))
                  (Finset.mem_univ i)
                have hm := mul_le_mul_of_nonneg_left (le_max_left (u i - t) 0) (hlam i).le
                linarith
              have hcommon : ∀ u i, choiceProb u lam i = lam i * ∫ t in Set.Iic (u i), F u t := by
                intro u i
                have h := hprimitive u i (u i)
                rw [Function.update_eq_self] at h
                rw [h, mul_assoc, ← integral_const_mul]
                congr 1
                apply setIntegral_congr_fun measurableSet_Iic
                intro t ht
                change t ≤ u i at ht
                dsimp [D, F]
                rw [← Real.exp_add]
                congr 1
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), max_eq_left (sub_nonneg.mpr ht)]
                ring
              have hFgap : ∀ u (k : Fin n) a b, u k ≤ a → a ≤ b →
                  F u b - F u a ≤ (L - lam k) * ∫ t in a..b, F u t := by
                intro u k a b hka hab
                let C := L - lam k
                have hC : 0 < C := hLminus k
                have hbound : ∀ t, a ≤ t → t ≤ b →
                    F u b * Real.exp (-(C * (b - t))) ≤ F u t := by
                  intro t hat htb
                  dsimp [F]
                  rw [← Real.exp_add]
                  apply Real.exp_le_exp.mpr
                  have hmaxlip : ∀ r : ℝ, max (r - t) 0 - max (r - b) 0 ≤ b - t := by
                    intro r
                    simp only [max_def]
                    split_ifs <;> linarith
                  have hs := Finset.sum_le_sum (s := Finset.univ.erase k) (fun j _ =>
                    mul_le_mul_of_nonneg_left (hmaxlip (u j)) (hlam j).le)
                  have hsum : (∑ j, lam j * max (u j - t) 0) - (∑ j, lam j * max (u j - b) 0) ≤ C * (b - t) := by
                    rw [← Finset.sum_sub_distrib]
                    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
                    simp only [max_eq_right (by linarith : u k - t ≤ 0),
                      max_eq_right (by linarith : u k - b ≤ 0), sub_self, mul_zero, add_zero]
                    have hsC : (∑ j ∈ Finset.univ.erase k, lam j * (b - t)) = C * (b - t) := by
                      rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ k)]
                    rw [hsC] at hs
                    simpa only [mul_sub] using hs
                  linarith
                let g : ℝ → ℝ := fun t => F u b * Real.exp (-(C * (b - t)))
                have hgcont : Continuous g := by dsimp [g]; fun_prop
                have hd : ∀ t, HasDerivAt g (C * g t) t := by
                  intro t
                  convert! (((((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul C).neg.exp).const_mul (F u b)) using 1 <;> simp [g] <;> ring
                have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
                  (fun t _ => hd t) ((continuous_const.mul hgcont).intervalIntegrable a b)
                rw [intervalIntegral.integral_const_mul] at hi
                have hm := intervalIntegral.integral_mono_on (μ := volume) hab (hgcont.intervalIntegrable a b)
                  ((hFcont u).intervalIntegrable a b) (fun t ht => hbound t ht.1 ht.2)
                have hm' := mul_le_mul_of_nonneg_left hm hC.le
                have hba := hbound a le_rfl hab
                simp only [g, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at hi
                linarith
              have hsymShare : ∀ u a, (∀ i, α i = a) → (∀ i, α i - u i = tau u lam i) →
                  ∀ i j, u i ≤ u j → choiceProb u lam j ≤ choiceProb u lam i := by
                intro u a ha hf i j hij
                obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ u
                  ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
                let C := L - lam k
                have hC : 0 < C := hLminus k
                have hbase : a - u k = 1 / C := by
                  rw [← ha k, hf k, htaulow u k (fun r => hk r (Finset.mem_univ r))]
                have hpi : 0 < a - u i := by rw [← ha i, hf i]; exact htaupos u i
                have hpj : 0 < a - u j := by rw [← ha j, hf j]; exact htaupos u j
                have hCpj : C * (a - u j) ≤ 1 := by
                  have hb : C * (a - u k) = 1 := by rw [hbase]; exact mul_one_div_cancel (ne_of_gt hC)
                  have hkj := hk j (Finset.mem_univ j)
                  nlinarith only [hb, hkj, hC]
                let A : ℝ := ∫ t in Set.Iic (u i), F u t
                let B : ℝ := ∫ t in u i..u j, F u t
                have hA : 0 < A := by
                  have hh := hQpos u i
                  rw [hcommon] at hh
                  exact (mul_pos_iff_of_pos_left (hlam i)).mp hh
                have hB : 0 ≤ B := by
                  apply intervalIntegral.integral_nonneg hij
                  intro t _
                  exact (Real.exp_pos _).le
                have hgap : F u (u j) - F u (u i) ≤ C * B :=
                  hFgap u k (u i) (u j) (hk i (Finset.mem_univ i)) hij
                have hmargin : ∀ r, (a - u r) * (F u (u r) - choiceProb u lam r) =
                    ∫ t in Set.Iic (u r), F u t := by
                  intro r
                  have hr := hf r
                  rw [ha r, tau, hpartial, hHF] at hr
                  have hden := ne_of_gt (hderivpos u r)
                  rw [hHF] at hden
                  have hr' := (eq_div_iff hden).mp hr
                  rw [hcommon] at hr'
                  have hr'' : lam r * ((a - u r) * (F u (u r) - choiceProb u lam r)) =
                      lam r * ∫ t in Set.Iic (u r), F u t := by
                    calc
                      _ = (a - u r) * (lam r * (F u (u r) - lam r * ∫ t in Set.Iic (u r), F u t)) := by rw [hcommon]; ring
                      _ = _ := hr'
                  exact mul_left_cancel₀ (ne_of_gt (hlam r)) hr''
                have hmi := hmargin i
                have hmj := hmargin j
                have hdiff : (∫ t in Set.Iic (u j), F u t) = A + B := by
                  have hh := intervalIntegral.integral_Iic_sub_Iic (hFint u (u i)) (hFint u (u j))
                  dsimp [A, B]
                  linarith
                rw [hdiff] at hmj
                change (a - u i) * (F u (u i) - choiceProb u lam i) = A at hmi
                have h₁ := mul_nonneg (show 0 ≤ (a - u i) - (a - u j) by linarith) hA.le
                have h₂ := mul_nonneg hpi.le (mul_nonneg (sub_nonneg.mpr hCpj) hB)
                have h₃ := mul_nonneg (mul_nonneg hpi.le hpj.le) (sub_nonneg.mpr hgap)
                have hmi' := congrArg (fun x : ℝ => (a - u j) * x) hmi
                have hmj' := congrArg (fun x : ℝ => (a - u i) * x) hmj
                have hres : (a - u i) * (a - u j) * (choiceProb u lam j - choiceProb u lam i) ≤ 0 := by
                  nlinarith only [h₁, h₂, h₃, hmi', hmj']
                by_contra h
                have hq : 0 < choiceProb u lam j - choiceProb u lam i := sub_pos.mpr (lt_of_not_ge h)
                exact not_lt_of_ge hres (mul_pos (mul_pos hpi hpj) hq)
              have hsymRateShare : ∀ u i j, lam i = lam j → u i ≤ u j →
                  choiceProb u lam i ≤ choiceProb u lam j := by
                intro u i j hl hij
                rw [hKbridge, hKbridge, hl, hHF, hHF]
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left (hFmono u hij) (hlam j).le
                · exact hKorder u u j i (fun k => by linarith)
                · exact (hKpos u i).le
                · exact mul_nonneg (hlam j).le (Real.exp_pos _).le
              refine ⟨?_, ?_, ?_⟩
              · rintro ⟨c, hc⟩ σ ha
                have hl : Antitone (fun s => lam (σ s)) := by
                  intro s t _
                  simp only [hc]
                  exact le_rfl
                refine ⟨hseqExists σ, ?_⟩
                intro u hu
                have hm := hseqMono σ ha hl u hu
                have hf := hseqFOC σ u hu hm
                have he := hseqNE σ ha hl u hu
                have hp : Monotone (fun s => eqPrices α β u (σ s)) := by
                  intro s t hst
                  dsimp [eqPrices]
                  rw [hf, hf]
                  apply div_le_div_of_nonneg_right _ hβ.le
                  apply htauorder
                  · exact hKorder u u (σ t) (σ s) (fun k => by linarith [hm hst])
                  · rw [hc, hc]
                have hq : Monotone (fun s => choiceProb (util α β (eqPrices α β u)) lam (σ s)) := by
                  rw [hpricesUtil]
                  intro s t hst
                  exact hsymRateShare u (σ s) (σ t) ((hc _).trans (hc _).symm) (hm hst)
                refine ⟨fun s => hcondroot (solvedBefore σ s.val) u (σ s), he,
                  fun p h => hNEuniq p _ h he, hp, hq, ?_⟩
                intro s t hst
                exact mul_le_mul (hp hst) (hq hst)
                  (hQpos _ _).le (he.1 _)
              · rintro ⟨a, ha⟩ σ hl
                have hα : Monotone (fun s => α (σ s)) := by
                  intro s t _
                  simp only [ha]
                  exact le_rfl
                refine ⟨hseqExists σ, ?_⟩
                intro u hu
                have hm := hseqMono σ hα hl u hu
                have hf := hseqFOC σ u hu hm
                have he := hseqNE σ hα hl u hu
                have hp : Antitone (fun s => eqPrices α β u (σ s)) := by
                  intro s t hst
                  dsimp [eqPrices]
                  rw [ha, ha]
                  exact div_le_div_of_nonneg_right (by linarith [hm hst]) hβ.le
                have hq : Antitone (fun s => choiceProb (util α β (eqPrices α β u)) lam (σ s)) := by
                  rw [hpricesUtil]
                  intro s t hst
                  exact hsymShare u a ha hf (σ s) (σ t) (hm hst)
                refine ⟨fun s => hcondroot (solvedBefore σ s.val) u (σ s), he,
                  fun p h => hNEuniq p _ h he, hp, hq, ?_⟩
                intro s t hst
                exact mul_le_mul (hp hst) (hq hst)
                  (hQpos _ _).le (he.1 _)
              · intro c a hc ha
                let p : Fin n → ℝ := fun _ => 1 / (β * c * ((n : ℝ) - 1))
                have hcpos : 0 < c := by rw [← hc ⟨0, by omega⟩]; exact hlam _
                have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
                have hnpos : (n : ℝ) ≠ 0 := by linarith
                have hnm1 : 0 < (n : ℝ) - 1 := by linarith
                have hLval : L = (n : ℝ) * c := by simp [L, hc]
                have huc : ∀ i j, util α β p i = util α β p j := by
                  intro i j
                  simp [util, p, ha]
                have he : IsPriceNE α β lam p := by
                  apply (hNEiff p).mpr
                  intro i
                  rw [htaulow (util α β p) i (fun j => (huc i j).le), hLval, hc i]
                  have hd : (n : ℝ) * c - c ≠ 0 := by
                    rw [← hLval, ← hc i]
                    exact ne_of_gt (hLminus i)
                  dsimp [p]
                  field_simp [ne_of_gt hβ, ne_of_gt hcpos, ne_of_gt hnm1, hd]
                  <;> ring
                refine ⟨he, fun q hq => hNEuniq q p hq he, ?_⟩
                intro i
                have hq : choiceProb (util α β p) lam i = 1 / n := by
                  rw [hKbridge, hKlow (util α β p) i (fun j => (huc i j).le)]
                  have hh : H (util α β p) i = 1 := by simp [H, util, p, ha]
                  rw [hh, hLval, hc i]
                  field_simp
                  <;> ring
                refine ⟨hq, ?_⟩
                change p i * choiceProb (util α β p) lam i = _
                rw [hq]
                dsimp [p]
                field_simp
                <;> ring

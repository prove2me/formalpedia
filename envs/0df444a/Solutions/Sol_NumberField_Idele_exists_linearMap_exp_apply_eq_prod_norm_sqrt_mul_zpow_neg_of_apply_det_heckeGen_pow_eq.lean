-- Prove2me | solution 1 for NumberField.Idele.exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2a22ffc5-9a96-569e-b875-7e64e535667a

import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
import Theorems.Thm_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
import Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v)
    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ f v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ f v = ζ v) :
    ∃ ℓ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ,
      ∀ φ : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero φ = 1) →
        ∀ k : Fin T.card → ℤ,
          (∀ j : Fin T.card,
            NumberField.Idele.ord K (T.equivFin.symm j).1
                (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) φ) =
              (f (T.equivFin.symm j).1 : ℤ) * k j) →
          Real.exp (ℓ fun i => (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
              Real.log (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) (φ : K))) =
            ∏ j : Fin T.card, ‖(Real.sqrt (Nw (T.equivFin.symm j).1 : ℝ) : ℂ) * s (T.equivFin.symm j).1‖ ^ (-(k j)) := by
  classical

  obtain ⟨w, hw⟩ :=
    AutomorphicForm.exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial K ξ hξc hξt
  refine ⟨((w - 1) / 2) • ∑ i : Fin (Fintype.card (NumberField.InfinitePlace K)), LinearMap.proj i, ?_⟩
  intro φ hφ k hk
  set z : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* (AdeleRing (𝓞 K) K)) φ with hz
  set e : Fin T.card → HeightOneSpectrum (𝓞 K) := fun j => (T.equivFin.symm j).1 with he
  have heT : ∀ j, e j ∈ T := fun j => (T.equivFin.symm j).2

  set X : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ := fun i =>
    (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
      Real.log (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) (φ : K)) with hX
  set SX : ℝ := ∑ i, X i with hSX
  have hℓ : (((w - 1) / 2) • ∑ i : Fin (Fintype.card (NumberField.InfinitePlace K)), LinearMap.proj i :
      (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) X = ((w - 1) / 2) * SX := by
    simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.proj_apply, smul_eq_mul, hSX]
  rw [hℓ]

  have hzval : (z : (AdeleRing (𝓞 K) K)) = algebraMap K (AdeleRing (𝓞 K) K) (φ : K) := rfl
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((z : (AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) v) =
        ((v.valuationOfNeZero φ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro v
    rw [hzval, NumberField.AdeleRing.algebraMap_snd_apply,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]

  have hzU : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one]
    intro v hv
    have hvT : v ∉ T := fun h => hv (Finset.mem_coe.mpr (Finset.mem_union_right S h))
    rw [hval v, hφ v hvT]
    rfl

  have hfact := NumberField.Idele.apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
    K ξ hξc S T hTS hur z hzU
  rw [hξt z ⟨φ, rfl⟩] at hfact

  have hordT : ∀ j : Fin T.card, NumberField.Idele.ord K (e j) z = (f (e j) : ℤ) * k j := fun j => hk j

  set P : ℝ := ‖((ξ ⟨NumberField.Idele.partAt K S z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ with hP
  have hPpos : 0 < P := norm_pos_iff.mpr (Units.ne_zero _)
  have hζpos : ∀ j, 0 < ‖ζ (e j)‖ := fun j => norm_pos_iff.mpr (hζ _ (heT j))

  have hT : (∏ v ∈ T, ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ NumberField.Idele.ord K v z) = ∏ j : Fin T.card, ‖ζ (e j)‖ ^ (k j) := by
    rw [← Finset.prod_coe_sort T (fun v => ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ NumberField.Idele.ord K v z)]
    refine Fintype.prod_equiv T.equivFin _ _ (fun v => ?_)
    have hv : (v : HeightOneSpectrum (𝓞 K)) = e (T.equivFin v) := by simp [he]
    rw [hv, hordT, zpow_mul, zpow_natCast, ← norm_pow, hx _ (heT _)]
  have hprod : P * ∏ j : Fin T.card, ‖ζ (e j)‖ ^ (k j) = 1 := by
    have h1 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) hfact
    simp only [Units.val_one, norm_one, Units.val_mul, norm_mul, Units.coe_prod, norm_prod,
      Units.val_zpow_eq_zpow_val, norm_zpow] at h1
    rw [hT] at h1
    rw [hP]
    exact h1.symm

  have hPw : P = NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K S z) ^ w := hw _

  have hS1 : ∀ v ∈ S, ‖((algebraMap K (AdeleRing (𝓞 K) K) (φ : K)).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
    intro v hv
    have hvT : v ∉ T := fun h => Finset.disjoint_left.mp hTS h hv
    rw [NumberField.AdeleRing.algebraMap_snd_apply]
    have h := NumberField.FinitePlace.norm_embedding' (v := v) (φ : K)
    rw [NumberField.FinitePlace.embedding_apply] at h
    rw [h, ← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq, hφ v hvT]
    rfl
  have hwpos : ∀ w' : NumberField.InfinitePlace K, 0 < w' (φ : K) := fun w' => w'.pos_iff.mpr (Units.ne_zero φ)
  have hnorm_inf : ∀ w' : NumberField.InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) (φ : K)).1 w'‖ = w' (φ : K) := by
    intro w'
    rw [NumberField.AdeleRing.algebraMap_fst_apply]
    first
      | exact NumberField.InfinitePlace.Completion.norm_coe _
      | (rw [show ((φ : K) : w'.Completion) = ((WithAbs.equiv w'.1).symm (φ : K) : w'.Completion) from rfl,
            NumberField.InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply])
  have hNexp : NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K S z) = Real.exp SX := by
    rw [hz, NumberField.TateGlobal.ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm K S φ,
      Finset.prod_eq_one (fun v hv => hS1 v hv), mul_one, hSX, Real.exp_sum]
    refine (Fintype.prod_equiv (Fintype.equivFin (NumberField.InfinitePlace K)).symm _ _ fun i => ?_).symm
    show Real.exp (X i) = ‖(algebraMap K (AdeleRing (𝓞 K) K) (φ : K)).1 ((Fintype.equivFin (NumberField.InfinitePlace K)).symm i)‖ ^
      ((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult
    rw [hnorm_inf, hX]
    show Real.exp ((((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
        Real.log (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) (φ : K))) = _
    rw [← Real.log_pow, Real.exp_log (pow_pos (hwpos _) _)]

  have hPF : SX = ∑ j : Fin T.card, (k j : ℝ) * Real.log (Nw (e j) : ℝ) := by
    obtain ⟨Λ, Log, hLog, -, hΛ, -, hsum, -⟩ :=
      NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul K T
    have hmem : Log φ ∈ Λ := (hΛ _).mpr ⟨φ, hφ, rfl⟩
    have h := hsum _ hmem
    rw [hLog] at h
    simp only at h

    have hord' : ∀ j : Fin T.card, ((Multiplicative.toAdd ((e j).valuationOfNeZero φ) : ℤ) : ℝ) = -((f (e j) : ℝ) * (k j : ℝ)) := by
      intro j
      have h1 : NumberField.Idele.ord K (e j) z = -Multiplicative.toAdd ((e j).valuationOfNeZero φ) := by
        show -WithZero.log (Valued.v (((z : (AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) (e j))) = _
        rw [hval]; rfl
      have h2 : Multiplicative.toAdd ((e j).valuationOfNeZero φ) = -((f (e j) : ℤ) * k j) := by
        rw [← hordT j, h1, neg_neg]
      rw [h2]; push_cast; ring
    rw [hSX, hX]
    refine h.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hord' j, hNwf _ (heT j)]
    push_cast
    rw [Real.log_pow]
    ring

  have hNwpos : ∀ j, 0 < (Nw (e j) : ℝ) := by
    intro j
    rw [hNwf _ (heT j)]
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (e j).ne_bot)) _
  have hsnorm : ∀ j, ‖s (e j)‖ = Real.sqrt ‖ζ (e j)‖ := by
    intro j
    rw [← hs _ (heT j), norm_pow, Real.sqrt_sq (norm_nonneg _)]
  have ha : ∀ j, ‖(Real.sqrt (Nw (e j) : ℝ) : ℂ) * s (e j)‖ = Real.sqrt (Nw (e j) : ℝ) * Real.sqrt ‖ζ (e j)‖ := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hsnorm]
  have hapos : ∀ j, 0 < Real.sqrt (Nw (e j) : ℝ) * Real.sqrt ‖ζ (e j)‖ := fun j =>
    mul_pos (Real.sqrt_pos.mpr (hNwpos j)) (Real.sqrt_pos.mpr (hζpos j))

  have hZ : ∑ j : Fin T.card, (k j : ℝ) * Real.log ‖ζ (e j)‖ = -(w * SX) := by
    have h1 : Real.log (∏ j : Fin T.card, ‖ζ (e j)‖ ^ (k j)) = ∑ j, (k j : ℝ) * Real.log ‖ζ (e j)‖ := by
      rw [Real.log_prod (s := Finset.univ) (fun j _ => (zpow_pos (hζpos j) _).ne')]
      exact Finset.sum_congr rfl fun j _ => Real.log_zpow _ _
    have h2 : ∏ j : Fin T.card, ‖ζ (e j)‖ ^ (k j) = P⁻¹ := by
      calc ∏ j : Fin T.card, ‖ζ (e j)‖ ^ (k j) = P⁻¹ * (P * ∏ j : Fin T.card, ‖ζ (e j)‖ ^ (k j)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hPpos.ne', one_mul]
        _ = P⁻¹ := by rw [hprod, mul_one]
    rw [← h1, h2, Real.log_inv, hPw, hNexp, Real.log_rpow (Real.exp_pos _), Real.log_exp]

  have hR : ∏ j : Fin T.card, ‖(Real.sqrt (Nw (e j) : ℝ) : ℂ) * s (e j)‖ ^ (-(k j)) =
      Real.exp (∑ j : Fin T.card, (-(k j : ℝ)) * (Real.log (Nw (e j) : ℝ) / 2 + Real.log ‖ζ (e j)‖ / 2)) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ha j]
    have hlog : Real.log (Real.sqrt (Nw (e j) : ℝ) * Real.sqrt ‖ζ (e j)‖) =
        Real.log (Nw (e j) : ℝ) / 2 + Real.log ‖ζ (e j)‖ / 2 := by
      rw [Real.log_mul (Real.sqrt_pos.mpr (hNwpos j)).ne' (Real.sqrt_pos.mpr (hζpos j)).ne',
        Real.log_sqrt (hNwpos j).le, Real.log_sqrt (norm_nonneg _)]
    rw [← hlog, ← Real.rpow_intCast _ (-(k j)), Real.rpow_def_of_pos (hapos j)]
    push_cast
    ring_nf
  show Real.exp ((w - 1) / 2 * SX) = ∏ j : Fin T.card, ‖(Real.sqrt (Nw (e j) : ℝ) : ℂ) * s (e j)‖ ^ (-(k j))
  rw [hR]
  congr 1
  have hsplit : ∑ j : Fin T.card, (-(k j : ℝ)) * (Real.log (Nw (e j) : ℝ) / 2 + Real.log ‖ζ (e j)‖ / 2) =
      -(1 / 2) * (∑ j : Fin T.card, (k j : ℝ) * Real.log (Nw (e j) : ℝ)) +
        -(1 / 2) * ∑ j : Fin T.card, (k j : ℝ) * Real.log ‖ζ (e j)‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, ← hPF, hZ]
  ring

end S_NumberField_Idele_exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
end P2MW
export P2MW.S_NumberField_Idele_exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq (solution)

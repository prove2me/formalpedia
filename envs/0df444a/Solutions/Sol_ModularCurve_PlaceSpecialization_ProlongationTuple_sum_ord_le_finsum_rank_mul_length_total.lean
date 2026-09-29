-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_le_finsum_rank_mul_length_total
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b48ea39d-2411-5b01-8387-45327b4ae828

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isIntegrallyClosed_nodeIntegersOver
import Theorems.Thm_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

universe u v

p2m_open "AlgebraicCurve IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve ModularCurve.UVCrossingModel~U_mul_V ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve.PlaceSpecialization"

namespace ENat p2m_export "ENat" "lift toNat one_le_iff_ne_zero coe_one map ne_top_iff_exists" end ENat
p2m_open_scoped "ENat" in

theorem ENat.sum_finsum_le_finsum_of_forall_imp_of_forall_eq
    {α : Type u} {X : Type v} (P : α → Prop) (C : X → α → Prop)
    (hCP : ∀ x a, C x a → P a) (hdisj : ∀ x x' a, C x a → C x' a → x = x')
    (F : α → ℕ∞) (hfin : {a | P a ∧ F a ≠ 0}.Finite) (T : Finset X) :
    (∑ x ∈ T, ∑ᶠ (a : α) (_ : C x a), F a) ≤ ∑ᶠ (a : α) (_ : P a), F a := by
  classical
  set S := hfin.toFinset with hS
  have hmemS : ∀ a, a ∈ S ↔ P a ∧ F a ≠ 0 := fun a => by rw [hS, Set.Finite.mem_toFinset]; rfl

  have hR : (∑ᶠ (a : α) (_ : P a), F a) = ∑ a ∈ S, (if P a then F a else 0) := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [finsum_eq_if]
    · intro a ha
      rw [Function.mem_support, finsum_eq_if] at ha
      rw [Finset.mem_coe, hmemS]
      by_cases hP : P a
      · rw [if_pos hP] at ha; exact ⟨hP, ha⟩
      · rw [if_neg hP] at ha; exact absurd rfl ha
  have hL : ∀ x, (∑ᶠ (a : α) (_ : C x a), F a) = ∑ a ∈ S, (if C x a then F a else 0) := by
    intro x
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [finsum_eq_if]
    · intro a ha
      rw [Function.mem_support, finsum_eq_if] at ha
      rw [Finset.mem_coe, hmemS]
      by_cases hC : C x a
      · rw [if_pos hC] at ha; exact ⟨hCP x a hC, ha⟩
      · rw [if_neg hC] at ha; exact absurd rfl ha
  rw [hR, Finset.sum_congr rfl (fun x _ => hL x), Finset.sum_comm]
  refine Finset.sum_le_sum fun a ha => ?_
  have hPa : P a := ((hmemS a).mp ha).1
  rw [if_pos hPa]

  by_cases hex : ∃ x ∈ T, C x a
  · obtain ⟨x, hxT, hxa⟩ := hex
    rw [Finset.sum_eq_single_of_mem x hxT]
    · rw [if_pos hxa]
    · intro y _ hyx
      rw [if_neg]
      intro hya
      exact hyx (hdisj y x a hya hxa)
  · push Not at hex
    rw [Finset.sum_eq_zero (fun y hy => if_neg (hex y hy))]
    exact zero_le

namespace LeTotGlue

theorem length_localizedModule_quotient_eq_zero {R : Type u} [CommRing R] (x : R) (Q : Ideal R) [Q.IsPrime]
    (hx : x ∉ Q) : Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ Ideal.span {x})) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine subsingleton_of_forall_eq 0 fun m => ?_
  induction m using LocalizedModule.induction_on with
  | h a s =>
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [Submonoid.smul_def, smul_zero]
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)

theorem sum_finsum_le_finsum_horizontal
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    {X : Type v} (T : Finset X) (κ : X → PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) → Prop)
    (hdisj : ∀ a b Q, κ a Q → κ b Q → a = b) :
    (∑ a ∈ T, ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ κ a Q),
        (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) := by
  refine ENat.sum_finsum_le_finsum_of_forall_imp_of_forall_eq
    (fun Q => Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal)
    (fun a Q => Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ κ a Q)
    (fun a Q h => ⟨h.1, h.2.1⟩) (fun a b Q h h' => hdisj a b Q h.2.2 h'.2.2) _ ?_ T
  refine (setOf_horizontal_mem_finite ϖ hϖ e he x hx).subset ?_
  rintro Q ⟨⟨h0, hc⟩, hF⟩
  refine ⟨h0, hc, ?_⟩
  by_contra hxQ
  apply hF
  rw [length_localizedModule_quotient_eq_zero x Q.asIdeal hxQ, mul_zero]

end LeTotGlue

namespace LeTotGlue

theorem mul_finsum_le_finsum_mul {α : Type u} (A B : α → Prop) (hAB : ∀ a, A a → B a) (hA : {a | A a}.Finite)
    (r m : α → ℕ∞) (ℓ : ℕ∞) (hℓ : ∀ a, A a → ℓ ≤ m a) (hfin : {a | B a ∧ r a * m a ≠ 0}.Finite) :
    ℓ * (∑ᶠ (a : α) (_ : A a), r a) ≤ ∑ᶠ (a : α) (_ : B a), r a * m a := by
  classical
  set S := hA.toFinset with hS
  have hmemS : ∀ a, a ∈ S ↔ A a := fun a => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hL : (∑ᶠ (a : α) (_ : A a), r a) = ∑ a ∈ S, r a := by
    rw [show (fun a => ∑ᶠ (_ : A a), r a) = fun a => ∑ᶠ (_ : a ∈ S), r a from
      funext fun a => by simp only [hmemS]]
    exact finsum_mem_finset_eq_sum r S
  have hM : (∑ᶠ (a : α) (_ : A a), r a * m a) = ∑ a ∈ S, r a * m a := by
    rw [show (fun a => ∑ᶠ (_ : A a), r a * m a) = fun a => ∑ᶠ (_ : a ∈ S), r a * m a from
      funext fun a => by simp only [hmemS]]
    exact finsum_mem_finset_eq_sum _ S
  calc ℓ * (∑ᶠ (a : α) (_ : A a), r a) = ∑ a ∈ S, ℓ * r a := by rw [hL, Finset.mul_sum]
    _ ≤ ∑ a ∈ S, r a * m a := Finset.sum_le_sum fun a ha => by
        rw [mul_comm]; exact mul_le_mul_right (hℓ a ((hmemS a).mp ha)) _
    _ = ∑ x ∈ ({()} : Finset Unit), ∑ᶠ (a : α) (_ : A a), r a * m a := by rw [Finset.sum_singleton, hM]
    _ ≤ ∑ᶠ (a : α) (_ : B a), r a * m a :=
        ENat.sum_finsum_le_finsum_of_forall_imp_of_forall_eq B (fun (_ : Unit) a => A a)
          (fun _ a h => hAB a h) (fun _ _ _ _ _ => rfl) _ hfin {()}

end LeTotGlue

namespace IsLocalRing p2m_export "IsLocalRing" "isField_iff_maximalIdeal_eq le_maximalIdeal ResidueField maximalIdeal residue_eq_zero_iff maximalIdeal.isMaximal of_injective residue eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.ne_bot_and_comap_eq_of_map_le
    {B : Type u} [CommRing B] [IsLocalRing B] {Rm : Type v} [CommRing Rm] [IsDomain Rm]
    (j : B →+* Rm) (hj : Function.Injective j)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (𝔮 : Ideal B) [𝔮.IsPrime] (f : B) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (Q : Ideal Rm) [Q.IsPrime] (hJQ : Ideal.map j 𝔮 ≤ Q) (hQm : ∃ b ∈ maximalIdeal B, j b ∉ Q) :
    Q ≠ ⊥ ∧ Q.comap j = 𝔮 := by
  have hjf : j f ∈ Q := hJQ (Ideal.mem_map_of_mem j hf𝔮)
  refine ⟨fun hQ => hf (hj ?_), ?_⟩
  · rw [map_zero]
    rw [hQ] at hjf
    exact (Ideal.mem_bot.mp hjf)
  · have hle : 𝔮 ≤ Q.comap j := Ideal.le_comap_of_map_le hJQ
    haveI : (Q.comap j).IsPrime := Ideal.IsPrime.comap j
    have hne : Q.comap j ≠ maximalIdeal B := by
      obtain ⟨b, hb, hbQ⟩ := hQm
      intro h
      exact hbQ (show b ∈ Q.comap j from h ▸ hb)
    by_contra hneq
    have hlt : 𝔮 < Q.comap j := lt_of_le_of_ne hle (Ne.symm hneq)
    have := hht 𝔮 (Q.comap j) inferInstance inferInstance hne hlt
    exact hf (by rw [this] at hf𝔮; exact (Ideal.mem_bot.mp hf𝔮))

p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.algebraMap_adicCompletion_injective (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    Function.Injective (algebraMap B (AdicCompletion (maximalIdeal B) B)) := by
  change Function.Injective (AdicCompletion.of (maximalIdeal B) B)
  exact AdicCompletion.of_injective (maximalIdeal B) B

section MultStep
p2m_open "IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.IsLocalRing"

namespace P1Arch

theorem length_localizedModule_quotient_span_singleton {A : Type u} [CommRing A] (p : Submonoid A) (a : A) :
    Module.length (Localization p) (LocalizedModule p (A ⧸ Ideal.span {a})) =
      Module.length (Localization p) (Localization p ⧸ Ideal.span {algebraMap A (Localization p) a}) := by

  rw [← (localizedQuotientEquiv p (Ideal.span {a} : Submodule A A)).length_eq]

  let e₀ : LocalizedModule p A ≃ₗ[A] Localization p :=
    IsLocalizedModule.iso p (Algebra.linearMap A (Localization p))
  let e : LocalizedModule p A ≃ₗ[Localization p] Localization p :=
    LinearEquiv.extendScalarsOfIsLocalization p (Localization p) e₀
  have he : ∀ x, e x = e₀ x := fun x => LinearEquiv.extendScalarsOfIsLocalization_apply p (Localization p) e₀ x
  have hmap : Submodule.map (e : LocalizedModule p A →ₗ[Localization p] Localization p)
      (Submodule.localized p (Ideal.span {a} : Submodule A A)) =
      (Ideal.span {algebraMap A (Localization p) a} : Submodule (Localization p) (Localization p)) := by
    change Submodule.map _ (Submodule.localized' (Localization p) p (LocalizedModule.mkLinearMap p A) (Submodule.span A {a})) = _
    rw [Submodule.localized'_span, Set.image_singleton, Submodule.map_span, Set.image_singleton, Ideal.span]
    congr 2
    change e (LocalizedModule.mk a 1) = _
    rw [he, IsLocalizedModule.iso_mk_one]
    rfl
  exact (Submodule.Quotient.equiv _ _ e hmap).length_eq

end P1Arch

namespace IsDiscreteValuationRing p2m_export "IsDiscreteValuationRing" "quotient mk irreducible_iff_uniformizer maximalIdeal addVal addVal_le_iff_dvd addVal_pow TFAE addVal_uniformizer addVal_eq_top_iff length_quotient_map_span_eq_length_mul_length" end IsDiscreteValuationRing
p2m_open_scoped "IsDiscreteValuationRing" in

theorem IsDiscreteValuationRing.length_localizedModule_quotient_le_of_comap_eq
    {B : Type u} [CommRing B] [IsDomain B] {R : Type v} [CommRing R] [IsDomain R]
    (j : B →+* R) (hj : Function.Injective j)
    (𝔮 : Ideal B) [𝔮.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔮)]
    (Q : Ideal R) [Q.IsPrime] (hcontr : Q.comap j = 𝔮) (f : B) (hf : f ≠ 0) :
    Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (B ⧸ Ideal.span {f})) ≤
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ Ideal.span {j f})) := by
  rw [P1Arch.length_localizedModule_quotient_span_singleton, P1Arch.length_localizedModule_quotient_span_singleton]
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors Q)
  let φ : Localization.AtPrime 𝔮 →+* Localization.AtPrime Q := Localization.localRingHom 𝔮 Q j hcontr.symm
  haveI : IsLocalHom φ := Localization.isLocalHom_localRingHom 𝔮 Q j hcontr.symm
  have hφ : ∀ d ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮), φ d ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    fun d hd => map_nonunit φ d hd
  have hφ0 : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m, hm⟩, hma⟩ := hx
    have hm0 : m ≠ 0 := fun h => hm (by rw [h]; exact Q.zero_mem)
    have hja : j y.1 = 0 := (mul_eq_zero.mp hma).resolve_left hm0
    have ha : y.1 = 0 := hj (by rw [hja, map_zero])
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨1, by rw [ha, mul_zero]⟩
  have hfD : algebraMap B (Localization.AtPrime 𝔮) f ≠ 0 := by
    intro h
    rw [IsLocalization.map_eq_zero_iff 𝔮.primeCompl] at h
    obtain ⟨⟨s, hs⟩, hsf⟩ := h
    have : j s * j f = 0 := by rw [← map_mul, hsf, map_zero]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hs (by rw [hj (by rw [h1, map_zero] : j s = j 0)]; exact 𝔮.zero_mem)
    · exact hf (hj (by rw [h1, map_zero]))
  have hmult := IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length φ hφ0 _ hfD
  rw [Localization.localRingHom_to_map] at hmult
  rw [hmult]

  have hne : Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) ≠ ⊤ := by
    intro h
    have hle : Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
      Ideal.map_le_iff_le_comap.mpr (fun d hd => hφ d hd)
    rw [h, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top hle
  haveI : Nontrivial (Localization.AtPrime Q ⧸ Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have h1 : 1 ≤ Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))) := by
    rw [ENat.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff]
    exact not_subsingleton _
  calc Module.length (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮 ⧸ Ideal.span {algebraMap B _ f})
      = Module.length (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮 ⧸ Ideal.span {algebraMap B _ f}) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_right h1 _

end MultStep

namespace SepAux

theorem isDiscreteValuationRing_localization {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (𝔮 : Ideal B) [𝔮.IsPrime] (hbot : 𝔮 ≠ ⊥)
    (hht : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → 𝔭 < 𝔮 → 𝔭 = ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔮) := by
  haveI : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl _ inferInstance
  have hinjB := IsLocalization.injective (Localization.AtPrime 𝔮) 𝔮.primeCompl_le_nonZeroDivisors
  have hunder : Ideal.under B (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) = 𝔮 :=
    IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime 𝔮) 𝔮
  have hnf : ¬ IsField (Localization.AtPrime 𝔮) := by
    intro hf
    apply hbot
    have h1 : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mp hf
    rw [← hunder, h1]
    exact Ideal.comap_bot_of_injective _ hinjB
  have hic : IsIntegrallyClosed (Localization.AtPrime 𝔮) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime 𝔮) 𝔮.primeCompl 𝔮.primeCompl_le_nonZeroDivisors
  have key : IsIntegrallyClosed (Localization.AtPrime 𝔮) ∧
      ∃! P : Ideal (Localization.AtPrime 𝔮), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨hic, IsLocalRing.maximalIdeal _, ⟨?_, inferInstance⟩, ?_⟩
    · exact fun h0 => hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h0)
    · rintro P ⟨hP0, hP⟩
      have hPq : Ideal.under B P ≤ 𝔮 :=
        (Ideal.comap_mono (f := algebraMap B (Localization.AtPrime 𝔮)) (IsLocalRing.le_maximalIdeal hP.ne_top)).trans_eq hunder
      have hPpr : (Ideal.under B P).IsPrime := Ideal.comap_isPrime _ P
      have hne : Ideal.under B P ≠ ⊥ := by
        intro h0
        apply hP0
        rw [← IsLocalization.map_comap 𝔮.primeCompl (Localization.AtPrime 𝔮) P]
        show Ideal.map _ (Ideal.under B P) = ⊥
        rw [h0, Ideal.map_bot]
      have heq : Ideal.under B P = 𝔮 := by
        rcases eq_or_lt_of_le hPq with h | h
        · exact h
        · exact absurd (hht _ hPpr h) hne
      rw [← IsLocalization.map_comap 𝔮.primeCompl (Localization.AtPrime 𝔮) P,
        ← IsLocalization.map_comap 𝔮.primeCompl (Localization.AtPrime 𝔮) (IsLocalRing.maximalIdeal _)]
      show Ideal.map _ (Ideal.under B P) = Ideal.map _ (Ideal.under B (IsLocalRing.maximalIdeal _))
      rw [heq, hunder]
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔮) hnf).out 0 3).mpr key

end SepAux

namespace LeTotGlue
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve ModularCurve.UVCrossingModel~U_mul_V"

theorem le_finsum_of_le_mul_finsum
    {B : Type v} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (j : B →+* UVCrossingModel W (π ^ E)) (hj : Function.Injective j)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (b₀ : B) (hb₀ : b₀ ∈ maximalIdeal B) (hjb₀ : j b₀ = const (π ^ E) π)
    (𝔮 : Ideal B) [𝔮.IsPrime] (hne : 𝔮 ≠ maximalIdeal B) (f : B) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (X : ℕ∞)
    (h1 : X ≤ Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (B ⧸ Ideal.span {f})) *
        ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map j 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal),
          (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞)) :
    X ≤ ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ Q.asIdeal.comap j = 𝔮),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {j f})) := by
  classical
  haveI : IsDomain (UVCrossingModel W (π ^ E)) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE).1
  refine h1.trans ?_
  have hjf0 : j f ≠ 0 := fun h0 => hf (hj (by rw [h0, map_zero]))
  have hcontr : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      Q.asIdeal ∈ (Ideal.map j 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal →
      Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ Q.asIdeal.comap j = 𝔮 := by
    rintro Q ⟨hQmin, hQπ⟩
    have hJQ : Ideal.map j 𝔮 ≤ Q.asIdeal := hQmin.1.2
    have hQm : ∃ b ∈ maximalIdeal B, j b ∉ Q.asIdeal := ⟨b₀, hb₀, fun h => hQπ (hjb₀ ▸ h)⟩
    obtain ⟨h0, hc⟩ := IsLocalRing.ne_bot_and_comap_eq_of_map_le j hj hht 𝔮 f hf hf𝔮 Q.asIdeal hJQ hQm
    exact ⟨h0, hQπ, hc⟩
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔮) :=
    SepAux.isDiscreteValuationRing_localization 𝔮 (fun h0 => hf (by rw [h0] at hf𝔮; exact Ideal.mem_bot.mp hf𝔮))
      fun 𝔭 h𝔭 hlt => hht 𝔭 𝔮 h𝔭 inferInstance hne hlt
  refine mul_finsum_le_finsum_mul
    (fun Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) =>
      Q.asIdeal ∈ (Ideal.map j 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal)
    (fun Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) =>
      Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ Q.asIdeal.comap j = 𝔮)
    hcontr ?_ _ _ _ ?_ ?_
  · refine (setOf_horizontal_mem_finite π hπ E hE (j f) hjf0).subset ?_
    intro Q hQ
    exact ⟨(hcontr Q hQ).1, hQ.2, hQ.1.1.2 (Ideal.mem_map_of_mem j hf𝔮)⟩
  · rintro Q hQ
    haveI := Q.2
    exact IsDiscreteValuationRing.length_localizedModule_quotient_le_of_comap_eq j hj 𝔮 Q.asIdeal (hcontr Q hQ).2.2 f hf
  · refine (setOf_horizontal_mem_finite π hπ E hE (j f) hjf0).subset ?_
    rintro Q ⟨⟨h0, hc, -⟩, hF⟩
    refine ⟨h0, hc, ?_⟩
    by_contra hxQ
    apply hF
    rw [length_localizedModule_quotient_eq_zero _ Q.asIdeal hxQ, mul_zero]

end LeTotGlue

namespace LeTotGlue
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve.PlaceSpecialization ModularCurve.UVCrossingModel~U_mul_V ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve.PlaceSpecialization.ProlongationTuple"

theorem sum_toNat_ord_le_finsum_of_comap_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime]
    (h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮)
    (f : ↥(R.nodeIntegersOver K w)) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧
      ∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0)
    (hne : 𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) :
    ((∑ V ∈ S, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (Q.asIdeal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))) = 𝔮),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {(ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) f})) := by
  haveI := R.isIntegrallyClosed_nodeIntegersOver K w
  refine le_finsum_of_le_mul_finsum π hπ E hE _
    (ι.injective.comp (IsLocalRing.algebraMap_adicCompletion_injective ↥(R.nodeIntegersOver K w)))
    hht (R.nodeConst K w ϖ) (by rw [hmax]; exact Ideal.subset_span (by simp)) hιϖ 𝔮 hne f hf hf𝔮 _ ?_
  exact R.sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero K w c ϖ hϖ0 hmax hres hVI
    hwss π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 f hf hf𝔮 S hS

end LeTotGlue

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr qExpand_qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel_jq frobeniusGeomLevel_jqN mem_valuationSubring_iff_pow_mem frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl coe_geomAut_coeffEmb coeffMap_jqModC coeffMap_jqNModC coeffMap_qExpand CharPReduction.constSeries NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel UVCrossingModel.ringKrullDim_le_two UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete NodeLocalized.isDiscreteValuationRing_coeffSubring coeffEmb_jq isCurveOver_modularFunctionFieldBar" namespace NodeLocalized p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver isDiscreteValuationRing_coeffSubring" end ModularCurve.NodeLocalized
p2m_open_scoped "ModularCurve ModularCurve.NodeLocalized" in

theorem ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring_of_charP
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) :=
  isDiscreteValuationRing_coeffSubring red
    (fun c => ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red c) K

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr qExpand_qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel_jq frobeniusGeomLevel_jqN mem_valuationSubring_iff_pow_mem frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl coe_geomAut_coeffEmb coeffMap_jqModC coeffMap_jqNModC coeffMap_qExpand CharPReduction.constSeries NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel UVCrossingModel.ringKrullDim_le_two UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete NodeLocalized.isDiscreteValuationRing_coeffSubring coeffEmb_jq isCurveOver_modularFunctionFieldBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst sp mk d0_j d0_j_pole d1 d0_jN_pole d0_jN"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "ValueIntegralityLaw mem_toValuationSubring_of_mem_nodeIntegers nodeIntegersOver nodeConst coe_nodeConst NodeCoordinates atkinLehnerBar R₁ mk ι mem_integersFst_iff R₂ residue₁_coeffMap mem_integersSnd_iff ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem isIntegrallyClosed_nodeIntegersOver exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

def quotientSubfield (B : Subring ↥(modularFunctionFieldBar (N * q))) : Subfield (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {z | ∃ x y : ↥(modularFunctionFieldBar (N * q)), x ∈ B ∧ y ∈ B ∧ y ≠ 0 ∧
    z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))}
  zero_mem' := ⟨0, 1, zero_mem B, one_mem B, one_ne_zero, by simp⟩
  one_mem' := ⟨1, 1, one_mem B, one_mem B, one_ne_zero, by simp⟩
  add_mem' := by
    rintro z₁ z₂ ⟨x₁, y₁, hx₁, hy₁, hy₁0, h₁⟩ ⟨x₂, y₂, hx₂, hy₂, hy₂0, h₂⟩
    refine ⟨x₁ * y₂ + x₂ * y₁, y₁ * y₂, add_mem (mul_mem hx₁ hy₂) (mul_mem hx₂ hy₁), mul_mem hy₁ hy₂,
      mul_ne_zero hy₁0 hy₂0, ?_⟩
    push_cast
    linear_combination ((y₂ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) * h₁ +
      ((y₁ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) * h₂
  mul_mem' := by
    rintro z₁ z₂ ⟨x₁, y₁, hx₁, hy₁, hy₁0, h₁⟩ ⟨x₂, y₂, hx₂, hy₂, hy₂0, h₂⟩
    refine ⟨x₁ * x₂, y₁ * y₂, mul_mem hx₁ hx₂, mul_mem hy₁ hy₂, mul_ne_zero hy₁0 hy₂0, ?_⟩
    push_cast
    linear_combination ((x₂ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) * h₁ +
      z₁ * ((y₁ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) * h₂
  neg_mem' := by
    rintro z ⟨x, y, hx, hy, hy0, h⟩
    exact ⟨-x, y, neg_mem hx, hy, hy0, by push_cast; linear_combination -h⟩
  inv_mem' := by
    rintro z ⟨x, y, hx, hy, hy0, h⟩
    by_cases hz : z = 0
    · exact ⟨0, 1, zero_mem B, one_mem B, one_ne_zero, by simp [hz]⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hz
      have : z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
        rw [h]; simp
      exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast hy0)
    refine ⟨y, x, hy, hx, hx0, ?_⟩
    have hxc : ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
      exact_mod_cast hx0
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

theorem mem_quotientSubfield_iff (B : Subring ↥(modularFunctionFieldBar (N * q))) (z : LaurentSeries (AlgebraicClosure ℚ)) :
    z ∈ quotientSubfield B ↔ ∃ x y : ↥(modularFunctionFieldBar (N * q)), x ∈ B ∧ y ∈ B ∧ y ≠ 0 ∧
      z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
  Iff.rfl

theorem mem_quotientSubfield_of_mem (B : Subring ↥(modularFunctionFieldBar (N * q)))
    {x : ↥(modularFunctionFieldBar (N * q))} (hx : x ∈ B) :
    ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ quotientSubfield B :=
  ⟨x, 1, hx, one_mem B, one_ne_zero, by simp⟩

variable (R : ProlongationTuple P)

theorem forall_mem_fieldOver_exists_of_mem
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    (jF jNqF : ↥(modularFunctionFieldBar (N * q)))
    (hjF : ((jF : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hjNqF : ((jNqF : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (N * q))
    (hj : jF ∈ R.nodeIntegersOver K w) (hjNq : jNqF ∈ R.nodeIntegersOver K w) :
    ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  intro z hz
  suffices h : NodeLocalized.fieldOver (N * q) K ≤ quotientSubfield (R.nodeIntegersOver K w) from h hz
  unfold NodeLocalized.fieldOver
  rw [Subfield.closure_le]
  rintro s (⟨o, rfl⟩ | rfl | rfl)
  ·
    obtain ⟨c, hcK⟩ := o
    have hcs : CharPReduction.constSeries K.toSubalgebra.toSubring ⟨c, hcK⟩ =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c := rfl
    rw [hcs]
    rcases A.mem_or_inv_mem c with hcA | hcA
    · refine ⟨_, 1, (R.nodeConst K w ⟨c, hcA, hcK⟩).2, one_mem _, one_ne_zero, ?_⟩
      simp only [OneMemClass.coe_one, mul_one]
      rfl
    · by_cases hc0 : c = 0
      · refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
        simp [hc0]
      have hinvK : c⁻¹ ∈ K.toSubalgebra.toSubring := show c⁻¹ ∈ K from inv_mem (show c ∈ K from hcK)
      refine ⟨1, _, one_mem _, (R.nodeConst K w ⟨c⁻¹, hcA, hinvK⟩).2, ?_, ?_⟩
      · intro h0
        have h1 : ((R.nodeConst K w ⟨c⁻¹, hcA, hinvK⟩ : ↥(R.nodeIntegersOver K w)) :
            ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [h0]
        rw [coe_nodeConst] at h1
        exact inv_ne_zero hc0 ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).injective
          (h1.trans (map_zero _).symm))
      · simp only [OneMemClass.coe_one, coe_nodeConst]
        change algebraMap _ _ c * algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  · rw [← hjF]; exact mem_quotientSubfield_of_mem _ hj
  · rw [← hjNqF]; exact mem_quotientSubfield_of_mem _ hjNq

section Generators

noncomputable def jBarN (N : ℕ) [NeZero N] : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

noncomputable def jNBarN (N : ℕ) [NeZero N] : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

theorem coe_jBarN_mul : ((jBarN (N * q) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
    jqModC (AlgebraicClosure ℚ) := coeffEmb_jq _

theorem coe_jNBarN_mul : ((jNBarN (N * q) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
    jqNModC (AlgebraicClosure ℚ) (N * q) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (N * q) jq) = _
  rw [coeffMap_qExpand, jqNModC]
  congr 1
  exact coeffEmb_jq _

theorem mem_integersFst_of_coe_eq_coeffMap (f : ↥(modularFunctionFieldBar (N * q))) (y : LaurentSeries A)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) : f ∈ R.R₁.integers := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := hfy ▸ f.2
  obtain ⟨h, -⟩ := R.residue₁_coeffMap y hy
  have hf : f = ⟨coeffMap A.subtype y, hy⟩ := Subtype.ext hfy
  rw [hf]; exact h

theorem mem_integersSnd_iff_atkinLehnerBar_mem (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.R₂.integers ↔ ProlongationTuple.atkinLehnerBar N q f ∈ R.R₁.integers :=
  (R.mem_integersSnd_iff f).trans (R.mem_integersFst_iff _).symm

theorem coeffMap_subtype_qExpand_jqModC (M : ℕ) [NeZero M] :
    coeffMap A.subtype (qExpand A M (jqModC A)) = qExpand (AlgebraicClosure ℚ) M (jqModC (AlgebraicClosure ℚ)) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem exists_coe_atkinLehnerBar_jBarN_eq [NeZero q] :
    ∃ y : LaurentSeries A, ((ProlongationTuple.atkinLehnerBar N q (jBarN (N * q)) : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y := by
  by_cases hex : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q), IsAtkinLehnerAutFull N q σ
  · have hAL := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex 1 inferInstance (one_dvd N)).1
    refine ⟨qExpand A (1 * q) (jqModC A), ?_⟩
    rw [coeffMap_subtype_qExpand_jqModC]
    have hge := coe_geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
      (atkinLehnerInvolutionFull N q) ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩
    have h1 : (⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ : modularFunctionFieldFull (N * q)) =
        ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :=
      Subtype.ext (qExpand_one_apply jq).symm
    have hσ : atkinLehnerInvolutionFull N q ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ =
        ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ := by
      rw [h1]; exact hAL
    rw [hσ] at hge
    refine hge.trans ?_
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) jq) = _
    rw [coeffMap_qExpand]
    congr 1
    exact coeffEmb_jq _
  · refine ⟨jqModC A, ?_⟩
    rw [coeffMap_jqModC]
    unfold ProlongationTuple.atkinLehnerBar
    rw [atkinLehnerInvolutionFull_eq_refl N q hex, ← AlgEquiv.aut_one, map_one, AlgEquiv.one_apply]
    exact coe_jBarN_mul

theorem exists_coe_atkinLehnerBar_jNBarN_eq [NeZero q] :
    ∃ y : LaurentSeries A, ((ProlongationTuple.atkinLehnerBar N q (jNBarN (N * q)) : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y := by
  by_cases hex : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q), IsAtkinLehnerAutFull N q σ
  · have hAL := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex N inferInstance (dvd_refl N)).2
    refine ⟨qExpand A N (jqModC A), ?_⟩
    rw [coeffMap_subtype_qExpand_jqModC]
    have hge := coe_geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
      (atkinLehnerInvolutionFull N q) ⟨qExpand ℚ (N * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (dvd_refl N) q)⟩
    rw [hAL] at hge
    refine hge.trans ?_
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N jq) = _
    rw [coeffMap_qExpand]
    congr 1
    exact coeffEmb_jq _
  · refine ⟨jqNModC A (N * q), ?_⟩
    rw [coeffMap_jqNModC]
    unfold ProlongationTuple.atkinLehnerBar
    rw [atkinLehnerInvolutionFull_eq_refl N q hex, ← AlgEquiv.aut_one, map_one, AlgEquiv.one_apply]
    exact coe_jNBarN_mul

theorem isAffineGeomPlace_frobOnPlacesGeomLevel_iff (v : Place k (modularFunctionFieldC k N)) :
    IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) ↔ IsAffineGeomPlace k N v := by
  unfold IsAffineGeomPlace
  rw [mem_frobOnPlacesGeomLevel_iff, mem_frobOnPlacesGeomLevel_iff,
    show jGeomGen k N = ⟨jqModC k, jqModC_mem k N⟩ from rfl, show jNGeomGen k N = ⟨jqNModC k N, jqNModC_mem k N⟩ from rfl,
    frobeniusGeomLevel_jq, frobeniusGeomLevel_jqN, ← mem_valuationSubring_iff_pow_mem (ℓ := q),
    ← mem_valuationSubring_iff_pow_mem (ℓ := q)]

theorem jBarN_mem_and_jNBarN_mem_of_reduceFst_eq (w : Place k (modularFunctionFieldC k N)) [DecidableEq k]
    (hwss : w ∈ ssPlaces q N k)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    jBarN (N * q) ∈ V.toValuationSubring ∧ jNBarN (N * q) ∈ V.toValuationSubring := by
  have haff : IsAffineGeomPlace k N w := hwss.2.1
  constructor
  ·
    set w₁ := V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα with hw₁
    have hsp : P.sp w₁ = w := hV
    have hnot : ¬ (P.sp w₁).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
      rw [hsp]; exact not_lt.2 (Place.ord_nonneg_of_mem _ haff.1)
    have hex : ∃ a : A, 0 < w₁.ord (jBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := by
      by_contra h
      push Not at h
      exact hnot (P.d0_j_pole w₁ h)
    obtain ⟨a, ha⟩ := hex
    have hne : jBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at ha; exact lt_irrefl _ ha
    have hmem₁ : jBarN N ∈ w₁.toValuationSubring := by
      have := Place.mem_of_ord_nonneg w₁ hne ha.le
      simpa using add_mem this (w₁.algebraMap_mem' (a : AlgebraicClosure ℚ))

    have hmemV : heckeAlphaBar (AlgebraicClosure ℚ) N q (jBarN N) ∈ V.toValuationSubring := by
      have h := hmem₁
      rw [hw₁, show (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).toValuationSubring =
        V.toValuationSubring.comap (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom from rfl,
        ValuationSubring.mem_comap] at h
      exact h
    have heq : heckeAlphaBar (AlgebraicClosure ℚ) N q (jBarN N) = jBarN (N * q) :=
      Subtype.ext (coe_heckeAlphaBar N q (jBarN N))
    rwa [heq] at hmemV
  ·
    set w₂ := V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ with hw₂
    have haff₂ : IsAffineGeomPlace k N (P.sp w₂) := by
      rcases P.d1 V with h | h
      ·
        have h' : w = frobOnPlacesGeomLevel k N data hKr (P.sp w₂) := hV.symm.trans h
        rw [h', isAffineGeomPlace_frobOnPlacesGeomLevel_iff] at haff
        exact haff
      ·
        have h' : frobOnPlacesGeomLevel k N data hKr w = P.sp w₂ := by rw [← hV]; exact h
        rw [← h', isAffineGeomPlace_frobOnPlacesGeomLevel_iff]
        exact haff
    have hnot : ¬ (P.sp w₂).ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) < 0 :=
      not_lt.2 (Place.ord_nonneg_of_mem _ haff₂.2)
    have hex : ∃ a : A, 0 < w₂.ord (jNBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := by
      by_contra h
      push Not at h
      exact hnot (P.d0_jN_pole w₂ h)
    obtain ⟨a, ha⟩ := hex
    have hne : jNBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at ha; exact lt_irrefl _ ha
    have hmem₂ : jNBarN N ∈ w₂.toValuationSubring := by
      have := Place.mem_of_ord_nonneg w₂ hne ha.le
      simpa using add_mem this (w₂.algebraMap_mem' (a : AlgebraicClosure ℚ))
    have hmemV : heckeBetaBar (AlgebraicClosure ℚ) N q (jNBarN N) ∈ V.toValuationSubring := by
      have h := hmem₂
      rw [hw₂, show (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).toValuationSubring =
        V.toValuationSubring.comap (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom from rfl,
        ValuationSubring.mem_comap] at h
      exact h
    have heq : heckeBetaBar (AlgebraicClosure ℚ) N q (jNBarN N) = jNBarN (N * q) := by
      apply Subtype.ext
      rw [coe_heckeBetaBar]
      show qExpand (AlgebraicClosure ℚ) q (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N jq)) =
        coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (N * q) jq)
      rw [coeffMap_qExpand, coeffMap_qExpand, qExpand_qExpand, qExpand_congr (Nat.mul_comm q N)]
    rwa [heq] at hmemV

theorem jBarN_mem_nodeIntegersOver_and (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) [DecidableEq k] (hwss : w ∈ ssPlaces q N k) :
    jBarN (N * q) ∈ R.nodeIntegersOver K w ∧ jNBarN (N * q) ∈ R.nodeIntegersOver K w := by
  obtain ⟨y₁, hy₁⟩ := exists_coe_atkinLehnerBar_jBarN_eq (A := A) (N := N) (q := q)
  obtain ⟨y₂, hy₂⟩ := exists_coe_atkinLehnerBar_jNBarN_eq (A := A) (N := N) (q := q)
  refine ⟨⟨⟨?_, ?_, fun V hV => (jBarN_mem_and_jNBarN_mem_of_reduceFst_eq w hwss V hV).1⟩, ?_⟩,
    ⟨⟨?_, ?_, fun V hV => (jBarN_mem_and_jNBarN_mem_of_reduceFst_eq w hwss V hV).2⟩, ?_⟩⟩
  · exact mem_integersFst_of_coe_eq_coeffMap R _ (jqModC A) (by rw [coeffMap_jqModC]; exact coe_jBarN_mul)
  · exact (mem_integersSnd_iff_atkinLehnerBar_mem R _).2 (mem_integersFst_of_coe_eq_coeffMap R _ y₁ hy₁)
  · rw [coe_jBarN_mul]
    exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
  · exact mem_integersFst_of_coe_eq_coeffMap R _ (jqNModC A (N * q)) (by rw [coeffMap_jqNModC]; exact coe_jNBarN_mul)
  · exact (mem_integersSnd_iff_atkinLehnerBar_mem R _).2 (mem_integersFst_of_coe_eq_coeffMap R _ y₂ hy₂)
  · rw [coe_jNBarN_mul]
    exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

end Generators

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.forall_mem_fieldOver_exists_mul_eq_of_mem_ssPlaces
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    [DecidableEq k] (hwss : w ∈ ssPlaces q N k) :
    ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
  forall_mem_fieldOver_exists_of_mem R K w (jBarN (N * q)) (jNBarN (N * q)) coe_jBarN_mul coe_jNBarN_mul
    (jBarN_mem_nodeIntegersOver_and R K w hwss).1 (jBarN_mem_nodeIntegersOver_and R K w hwss).2

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "forall_mem_fieldOver_exists_mul_eq_of_mem_ssPlaces"
end ModularCurve.PlaceSpecialization.ProlongationTuple

namespace PlaceDepthAux

p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve ModularCurve.UVCrossingModel~U_mul_V"

section Model
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

noncomputable def residueMap (π : W) (E : ℕ) (hE : 1 ≤ E) : UVCrossingModel W (π ^ E) →+* W ⧸ Ideal.span {π} :=
  Ideal.Quotient.lift (uvCrossingIdeal W (π ^ E))
    ((Ideal.Quotient.mk (Ideal.span {π})).comp MvPowerSeries.constantCoeff) (by
      intro F hF
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
      · rintro _ ⟨rfl⟩
        simp only [RingHom.comp_apply, map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C]
        rw [map_zero, zero_mul, zero_sub, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton π)) E hE
      · exact map_zero _
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])

theorem residueMap_mk (π : W) (E : ℕ) (hE : 1 ≤ E) (F : MvPowerSeries (Fin 2) W) :
    residueMap π E hE (mk (π ^ E) F) = Ideal.Quotient.mk (Ideal.span {π}) (MvPowerSeries.constantCoeff F) := rfl

theorem not_isUnit_of_residueMap_eq_zero (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (x : UVCrossingModel W (π ^ E)) (hx : residueMap π E hE x = 0) : ¬ IsUnit x := by
  intro hu
  have hmax : (Ideal.span {π} : Ideal W).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]; exact IsLocalRing.maximalIdeal.isMaximal W
  haveI : Nontrivial (W ⧸ Ideal.span {π}) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  exact not_isUnit_zero (hx ▸ hu.map (residueMap π E hE))

theorem V_not_isUnit (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) : ¬ IsUnit (V (π ^ E)) :=
  not_isUnit_of_residueMap_eq_zero π hπ E hE _ (by
    change residueMap π E hE (mk (π ^ E) (MvPowerSeries.X 1)) = 0
    rw [residueMap_mk, MvPowerSeries.constantCoeff_X, map_zero])

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem U_mul_V (π : W) (E : ℕ) : U (π ^ E) * V (π ^ E) = const (π ^ E) (π ^ E) := by
  change mk (π ^ E) (MvPowerSeries.X 0) * mk (π ^ E) (MvPowerSeries.X 1) = mk (π ^ E) (MvPowerSeries.C (π ^ E))
  rw [← map_mul]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem const_pow (π : W) (E : ℕ) (w : W) (n : ℕ) : const (π ^ E) (w ^ n) = const (π ^ E) w ^ n := by
  change mk (π ^ E) (MvPowerSeries.C (w ^ n)) = mk (π ^ E) (MvPowerSeries.C w) ^ n
  rw [map_pow, map_pow]

theorem eq_zero_of_const_eq_zero (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) (w : W)
    (hw : const (π ^ E) w = 0) : w = 0 := by
  classical
  have hmem : (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) ∈ uvCrossingIdeal W (π ^ E) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  set s : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hs
  have hXX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 = MvPowerSeries.monomial s 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) =
      (if s ≤ m then MvPowerSeries.coeff (m - s) g else 0) - π ^ E * MvPowerSeries.coeff m g := by
    intro m
    rw [← hg, mul_comm, sub_mul, hXX, map_sub, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_C_mul, one_mul]
  have hs0 : ¬ s ≤ 0 := by
    intro h
    have := h 0
    simp [hs] at this
  have hsn : ∀ n : ℕ, (n + 1) • s ≠ 0 := by
    intro n h
    have := Finsupp.ext_iff.mp h 0
    simp [hs] at this
  have h0 : w = -(π ^ E * MvPowerSeries.coeff 0 g) := by
    have := hcoeff 0
    rw [MvPowerSeries.coeff_C, if_pos rfl, if_neg hs0, zero_sub] at this
    exact this
  have hrec : ∀ n : ℕ, MvPowerSeries.coeff (n • s) g = π ^ E * MvPowerSeries.coeff ((n + 1) • s) g := by
    intro n
    have := hcoeff ((n + 1) • s)
    rw [MvPowerSeries.coeff_C, if_neg (hsn n), if_pos (by rw [succ_nsmul]; exact le_add_self),
      show (n + 1) • s - s = n • s by rw [succ_nsmul, add_tsub_cancel_right]] at this
    exact (sub_eq_zero.mp this.symm)
  have hdiv : ∀ n : ℕ, MvPowerSeries.coeff 0 g = (π ^ E) ^ n * MvPowerSeries.coeff (n • s) g := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul, zero_nsmul]
    | succ n ih => rw [ih, hrec n, pow_succ, mul_assoc]

  have hg0 : MvPowerSeries.coeff 0 g = 0 := by
    by_contra hne
    have htop : IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff 0 g) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    have hle : ((E * (m + 1) : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff 0 g) := by
      have hd : (π ^ E) ^ (m + 1) ∣ MvPowerSeries.coeff 0 g := ⟨_, hdiv (m + 1)⟩
      have := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hd
      rwa [← pow_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ,
        nsmul_eq_mul, mul_one] at this
    rw [← hm] at hle
    have : E * (m + 1) ≤ m := by exact_mod_cast hle
    nlinarith
  rw [h0, hg0, mul_zero, neg_zero]

end Model

end PlaceDepthAux

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr qExpand_qExpand jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel_jq frobeniusGeomLevel_jqN mem_valuationSubring_iff_pow_mem frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl coe_geomAut_coeffEmb coeffMap_jqModC coeffMap_jqNModC coeffMap_qExpand CharPReduction.constSeries NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel UVCrossingModel.ringKrullDim_le_two UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete NodeLocalized.isDiscreteValuationRing_coeffSubring coeffEmb_jq isCurveOver_modularFunctionFieldBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst sp mk d0_j d0_j_pole d1 d0_jN_pole d0_jN"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "ValueIntegralityLaw mem_toValuationSubring_of_mem_nodeIntegers nodeIntegersOver nodeConst coe_nodeConst NodeCoordinates atkinLehnerBar R₁ mk ι mem_integersFst_iff R₂ residue₁_coeffMap mem_integersSnd_iff ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem isIntegrallyClosed_nodeIntegersOver exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

section SepGlue

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem isRational_of_place (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : V.IsRational := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
  exact (AlgebraicCurve.Place.isRational_iff_deg_eq_one V).2 (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed V)

theorem valuation_sub_evalAt_lt_one (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ V.toValuationSubring) :
    V.toValuationSubring.valuation
      (f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt f)) < 1 := by
  have hV := isRational_of_place V
  have hmem : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt f) ∈ V.toValuationSubring :=
    sub_mem hf (V.algebraMap_mem' _)
  rw [show (f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt f)) =
      ((⟨_, hmem⟩ : V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q))) from rfl,
    ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff]
  have h1 := V.algebraMap_evalAt hV hf
  have h2 := V.residue_algebraMap (V.evalAt f)
  have : (⟨_, hmem⟩ : V.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap (AlgebraicClosure ℚ) _ (V.evalAt f), V.algebraMap_mem' _⟩ := rfl
  rw [this, map_sub, sub_eq_zero, ← h1]
  exact h2.symm

theorem evalAt_eq_zero_iff (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ V.toValuationSubring) :
    V.evalAt f = 0 ↔ V.toValuationSubring.valuation f < 1 := by
  have hV := isRational_of_place V
  rw [show (f : ↥(modularFunctionFieldBar (N * q))) = ((⟨f, hf⟩ : V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q))) from rfl,
    ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, ← V.algebraMap_evalAt hV hf,
    map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective]

end SepGlue

end ModularCurve.PlaceSpecialization.ProlongationTuple

set_option maxHeartbeats 6400000 in
open AlgebraicCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total.ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (f : ↥(R.nodeIntegersOver K w)) (hf : f ≠ 0)
    (Ttot : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTtot : ∀ V, V ∈ Ttot ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w)) :
    ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by
  classical

  have hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥ :=
    IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two ι
      (ModularCurve.UVCrossingModel.ringKrullDim_le_two π hπ E hE)

  haveI hdvrO : IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K) :=
    ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring_of_charP red K
  have hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ} :=
    R.maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const K w ϖ π hπ E hE ι hιϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply PlaceDepthAux.eq_zero_of_const_eq_zero π hπ E hE π
    rw [← hιϖ, h0, map_zero, map_zero, map_zero]
  obtain ⟨τ, hτ, hτϖ⟩ :=
    R.exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const K w ϖ hϖgen hres π hπ E hE ι hιϖ

  have hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
    R.forall_mem_fieldOver_exists_mul_eq_of_mem_ssPlaces K w hwss

  have hmemV : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.reduceFst V = w →
      ∀ g : ↥(R.nodeIntegersOver K w), (g : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    fun V hV g => R.mem_toValuationSubring_of_mem_nodeIntegers g.2.1 hV
  let ker : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Ideal ↥(R.nodeIntegersOver K w) := fun V =>
    if hV : P.reduceFst V = w then
      (IsLocalRing.maximalIdeal ↥V.toValuationSubring).comap
        ((R.nodeIntegersOver K w).subtype.codRestrict V.toValuationSubring.toSubring (fun g => hmemV V hV g))
    else ⊥
  have hker : ∀ V, P.reduceFst V = w → ∀ g : ↥(R.nodeIntegersOver K w),
      g ∈ ker V ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0 := by
    intro V hV g
    simp only [ker, dif_pos hV, Ideal.mem_comap]
    rw [ValuationSubring.valuation_lt_one_iff, evalAt_eq_zero_iff V (hmemV V hV g)]
    rfl
  have hkerV : ∀ V ∈ Ttot, P.reduceFst V = w ∧ (ker V).IsPrime ∧
      ker V ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) ∧
      (∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ ker V) ∧ f ∈ ker V := by
    intro V hV
    obtain ⟨hord, hVw⟩ := (hTtot V).mp hV
    obtain ⟨h1, h2, h3, h4⟩ :=
      R.ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem K w V hVw (ker V) (hker V hVw)
    exact ⟨hVw, h1, h2, h3, h4 f hord⟩

  have hsplit : (∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat) =
      ∑ 𝔮 ∈ Ttot.image ker, ∑ V ∈ Ttot.filter (fun V => ker V = 𝔮),
        (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat :=
    (Finset.sum_fiberwise_of_maps_to (fun V hV => Finset.mem_image_of_mem ker hV) _).symm

  have hper : ∀ 𝔮 ∈ Ttot.image ker,
      ((∑ V ∈ Ttot.filter (fun V => ker V = 𝔮), (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (Q.asIdeal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))) = 𝔮),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by
    intro 𝔮 h𝔮T
    obtain ⟨V₀, hV₀, rfl⟩ := Finset.mem_image.mp h𝔮T
    obtain ⟨hV₀w, hpr, hne, hcst, hfV⟩ := hkerV V₀ hV₀
    haveI := hpr
    exact LeTotGlue.sum_toNat_ord_le_finsum_of_comap_eq R K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx
      hht hfrac hϖgen τ hτ hτϖ (ker V₀) hcst f hf hfV (Ttot.filter (fun V => ker V = ker V₀))
      (fun V hV => by
        rw [Finset.mem_filter] at hV
        obtain ⟨hVw, -, -, -, -⟩ := hkerV V hV.1
        exact ⟨hVw, fun g => hV.2 ▸ hker V hVw g⟩) hne

  have hjf : ι (algebraMap _ _ f) ≠ 0 := fun h0 => hf
    ((ι.injective.comp (IsLocalRing.algebraMap_adicCompletion_injective ↥(R.nodeIntegersOver K w))) (by
      show (ι.toRingHom.comp (algebraMap _ _)) f = (ι.toRingHom.comp (algebraMap _ _)) 0
      rw [map_zero]; exact h0))
  have hregroup := LeTotGlue.sum_finsum_le_finsum_horizontal π hπ E hE (ι (algebraMap _ _ f)) hjf (Ttot.image ker)
    (fun 𝔮 Q => Q.asIdeal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) = 𝔮)
    (fun a b Q ha hb => ha.symm.trans hb)

  calc ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞)
      = ∑ 𝔮 ∈ Ttot.image ker, ((∑ V ∈ Ttot.filter (fun V => ker V = 𝔮),
          (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) := by rw [hsplit]; push_cast; rfl
    _ ≤ _ := Finset.sum_le_sum hper
    _ ≤ _ := hregroup

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total (solution)

-- Prove2me | solution 1 for ModularCurve.exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f52c9c94-50a4-5da6-b3e2-b1b765149ba1

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
import Theorems.Thm_RingHom_mem_map_of_powerSeries_map_eq_of_forall_coeff_mem
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LaurentSeries
p2m_open "LaurentSeries"

variable {A L : Type*} [CommRing A] [CommRing L]

def truncToPowerSeries' (x : LaurentSeries L) : PowerSeries L := PowerSeries.mk fun n => x.coeff n

@[scoped simp] theorem coeff_truncToPowerSeries' (x : LaurentSeries L) (n : ℕ) :
    PowerSeries.coeff n (truncToPowerSeries' x) = x.coeff n := by
  rw [truncToPowerSeries', PowerSeries.coeff_mk]

theorem ofPowerSeries_truncToPowerSeries' {x : LaurentSeries L} (hx : 0 ≤ x.order) :
    HahnSeries.ofPowerSeries ℤ L (truncToPowerSeries' x) = x := by
  ext k
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_truncToPowerSeries']
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    · by_cases hx0 : x = 0
      · rw [hx0]; rfl
      · exact (HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk hx)).symm
    · rintro ⟨n, hn⟩
      simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Nat.castOrderEmbedding_apply] at hn
      omega

private def _root_.RingHom.codRestrictPowerSeries' (f : A →+* LaurentSeries L) (hf : ∀ a, 0 ≤ (f a).order) :
    A →+* PowerSeries L where
  toFun a := truncToPowerSeries' (f a)
  map_one' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries' (hf 1), map_one, map_one]
  map_mul' a b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries' (hf (a * b)), map_mul, map_mul,
      ofPowerSeries_truncToPowerSeries' (hf a), ofPowerSeries_truncToPowerSeries' (hf b)]
  map_zero' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries' (hf 0), map_zero, map_zero]
  map_add' a b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries' (hf (a + b)), map_add, map_add,
      ofPowerSeries_truncToPowerSeries' (hf a), ofPowerSeries_truncToPowerSeries' (hf b)]

p2m_alias "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.RingHom.codRestrictPowerSeries'" "RingHom.codRestrictPowerSeries'"
private theorem _root_.RingHom.ofPowerSeries_codRestrictPowerSeries' (f : A →+* LaurentSeries L)
    (hf : ∀ a, 0 ≤ (f a).order) (a : A) :
    HahnSeries.ofPowerSeries ℤ L (f.codRestrictPowerSeries' hf a) = f a :=
  ofPowerSeries_truncToPowerSeries' (hf a)

p2m_alias "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.RingHom.ofPowerSeries_codRestrictPowerSeries'" "RingHom.ofPowerSeries_codRestrictPowerSeries'"
@[scoped simp] private theorem _root_.RingHom.coeff_codRestrictPowerSeries' (f : A →+* LaurentSeries L)
    (hf : ∀ a, 0 ≤ (f a).order) (a : A) (n : ℕ) :
    PowerSeries.coeff n (f.codRestrictPowerSeries' hf a) = (f a).coeff n :=
  coeff_truncToPowerSeries' _ _

p2m_alias "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.RingHom.coeff_codRestrictPowerSeries'" "RingHom.coeff_codRestrictPowerSeries'"
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries.RingHom"
end LaurentSeries
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries"

namespace RingHom p2m_export "RingHom" "snd Smooth coe_mk ker_isPrime IsIntegral charZero ker_ne_top ext comp_apply mk ker id comp mem_ker fst mem_map_of_powerSeries_map_eq_of_forall_coeff_mem codRestrictPowerSeries' ofPowerSeries_codRestrictPowerSeries' coeff_codRestrictPowerSeries'" end RingHom
p2m_open_scoped "RingHom" in
theorem RingHom.ker_le_ker_of_ker_le_span_sup_sq_of_map_eq_zero
    {R R' L : Type*} [CommRing R] [Nontrivial R] [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    [CommRing L] [IsDomain L]
    (π : R' →+* R) (κ : R' →+* L) (t : R') (ht : κ t = 0)
    (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2) :
    RingHom.ker π ≤ RingHom.ker κ := by
  set I : Ideal R' := RingHom.ker π with hIdef
  set P : Ideal R' := RingHom.ker κ with hPdef
  haveI hP : P.IsPrime := RingHom.ker_isPrime κ
  have htP : t ∈ P := by simpa [hPdef, RingHom.mem_ker] using ht
  set mk : R' →+* R' ⧸ P := Ideal.Quotient.mk P with hmk
  have hmkt : mk t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr htP

  have hle : I.map mk ≤ I.map mk ^ 2 := by
    calc I.map mk ≤ (Ideal.span {t} ⊔ I ^ 2).map mk := Ideal.map_mono hcot
      _ = (Ideal.span {t}).map mk ⊔ (I ^ 2).map mk := Ideal.map_sup _ _ _
      _ = I.map mk ^ 2 := by
        rw [Ideal.map_span, Set.image_singleton, hmkt, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq,
          Ideal.map_pow]
  have hidem : IsIdempotentElem (I.map mk) := by
    change I.map mk * I.map mk = I.map mk
    rw [← pow_two]
    exact le_antisymm (Ideal.pow_le_self two_ne_zero) hle
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top (I.map mk) (IsNoetherian.noetherian _)).mp hidem with h | h
  ·
    have := (Ideal.map_eq_bot_iff_le_ker mk).mp h
    rwa [hmk, Ideal.mk_ker] at this
  ·
    exfalso
    have h1 : (1 : R' ⧸ P) ∈ I.map mk := by rw [h]; trivial
    obtain ⟨i, hi, hi1⟩ := (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp h1
    have hi2 : i - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hmk, map_sub, hi1, map_one, sub_self]
    have hIm : I ≤ IsLocalRing.maximalIdeal R' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
    have hPm : P ≤ IsLocalRing.maximalIdeal R' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top κ)
    have h3 : (1 : R') ∈ IsLocalRing.maximalIdeal R' := by
      have : (1 : R') = i - (i - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (hIm hi) (hPm hi2)
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h3

end
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries"

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar modularFunctionFieldFull IsPlaceReductionModL modularFunctionFieldFullC baseChangeEquiv cuspInftyFull order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull"
p2m_open "ModularCurve"
namespace QSatStalk

def qexp {N : ℕ} (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull N))
    (x : closedPoints M.C) : M.C.presheaf.stalk x.1 →+* LaurentSeries ℚ :=
  ((SubringClass.subtype (ModularCurve.modularFunctionFieldFull N)).comp M.ffEquiv.symm.toRingHom).comp
    (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)

theorem qexp_apply {N : ℕ} (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull N))
    (x : closedPoints M.C) (g : M.C.presheaf.stalk x.1) :
    qexp M x g = ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
      ↥(ModularCurve.modularFunctionFieldFull N)) : LaurentSeries ℚ) := rfl

theorem coe_algebraMap_full (N : ℕ) (q : ℚ) :
    ((algebraMap ℚ ↥(ModularCurve.modularFunctionFieldFull N) q :
      ↥(ModularCurve.modularFunctionFieldFull N)) : LaurentSeries ℚ) = HahnSeries.C q := by
  haveI : CharZero (LaurentSeries ℚ) := algebraRat.charZero _
  haveI : CharZero ↥(ModularCurve.modularFunctionFieldFull N) := algebraRat.charZero _
  rw [eq_ratCast (algebraMap ℚ ↥(ModularCurve.modularFunctionFieldFull N)) q, SubfieldClass.coe_ratCast,
    eq_ratCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) q]

theorem main (N : ℕ) [NeZero N]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Nontrivial R] [Algebra R ℚ]
    (hinj : Function.Injective (algebraMap R ℚ))
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension 1 c]
    (M₀ : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull N))
    (g : M₀.C ⟶ X) (hg : g ≫ c = M₀.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))
    (x₀ : closedPoints M₀.C) (hx₀ : M₀.placeOfPoint x₀ = ModularCurve.cuspInftyFull N)
    (ξ : X) (hspec : g.base x₀.1 ⤳ ξ)
    (π : X.presheaf.stalk ξ →+* R)
    (hπι : ∀ r : R, π ((X.presheaf.germ ⊤ ξ trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = r)
    (t : X.presheaf.stalk ξ) (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (u : PowerSeries R)
    (hu : qexp M₀ x₀ ((g.stalkMap x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom t)) =
        HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap R ℚ)))
    (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u))
    (a : R) (z : X.presheaf.stalk ξ) (P : PowerSeries R)
    (hP : qexp M₀ x₀ ((g.stalkMap x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom z)) =
        HahnSeries.ofPowerSeries ℤ ℚ ((a • P).map (algebraMap R ℚ))) :
    ∃ z' : X.presheaf.stalk ξ,
      z = (X.presheaf.germ ⊤ ξ trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) * z' := by
  classical

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c

  set ιR : R →+* X.presheaf.stalk ξ := (X.presheaf.germ ⊤ ξ trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) with hιR
  have hιR_apply : ∀ r, ιR r = (X.presheaf.germ ⊤ ξ trivial).hom (c.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := fun r => rfl
  have hπ : π.comp ιR = RingHom.id R := RingHom.ext fun r => hπι r

  set route : X.presheaf.stalk ξ →+* M₀.C.presheaf.stalk x₀.1 :=
    (g.stalkMap x₀.1).hom.comp (X.presheaf.stalkSpecializes hspec).hom with hroute
  set f : X.presheaf.stalk ξ →+* LaurentSeries ℚ := (qexp M₀ x₀).comp route with hf
  have hf_apply : ∀ w, f w = qexp M₀ x₀ ((g.stalkMap x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom w)) :=
    fun w => rfl
  have h0 : ∀ w, 0 ≤ (f w).order := fun w =>
    ModularCurve.order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull N M₀ x₀ hx₀ (route w)
  set e : X.presheaf.stalk ξ →+* PowerSeries ℚ := f.codRestrictPowerSeries' h0 with he
  have he' : ∀ w, HahnSeries.ofPowerSeries ℤ ℚ (e w) = f w := fun w =>
    f.ofPowerSeries_codRestrictPowerSeries' h0 w

  have hconst : ∀ r : R, f (ιR r) = HahnSeries.C (algebraMap R ℚ r) := by
    intro r

    have h1 : ∀ w : Γ(X, ⊤), (X.presheaf.stalkSpecializes hspec).hom ((X.presheaf.germ ⊤ ξ trivial).hom w) =
        (X.presheaf.germ ⊤ (g.base x₀.1) trivial).hom w := by
      intro w
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

    have h2 : ∀ w : Γ(X, ⊤), (g.stalkMap x₀.1).hom ((X.presheaf.germ ⊤ (g.base x₀.1) trivial).hom w) =
        (M₀.C.presheaf.germ ⊤ x₀.1 trivial).hom (g.appTop.hom w) := by
      intro w
      have h := congrArg (fun φ => φ.hom w) (Scheme.Hom.germ_stalkMap g ⊤ x₀.1 trivial)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
      rw [h]
      rfl

    have h3 : ∀ v : Γ(Spec (CommRingCat.of R), ⊤), g.appTop.hom (c.appTop.hom v) =
        M₀.toBase.appTop.hom ((Spec.map (CommRingCat.ofHom (algebraMap R ℚ))).appTop.hom v) := by
      intro v
      change (c.appTop ≫ g.appTop).hom v =
        ((Spec.map (CommRingCat.ofHom (algebraMap R ℚ))).appTop ≫ M₀.toBase.appTop).hom v
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hg]

    have h4 : (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom (algebraMap R ℚ r) := by
      have h := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R ℚ)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      rw [← h]

    have h5 : ∀ w : Γ(M₀.C, ⊤), algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
        ((M₀.C.presheaf.germ ⊤ x₀.1 trivial).hom w) = (M₀.C.presheaf.germ ⊤ (genericPoint M₀.C) trivial).hom w := by
      intro w
      change (M₀.C.presheaf.germ ⊤ x₀.1 trivial ≫ M₀.C.presheaf.stalkSpecializes _).hom w = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]

    have h6 : ∀ q : ℚ, M₀.ffEquiv.symm ((M₀.C.presheaf.germ ⊤ (genericPoint M₀.C) trivial).hom
        (M₀.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom q))) =
        algebraMap ℚ ↥(ModularCurve.modularFunctionFieldFull N) q := by
      intro q
      apply M₀.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply, M₀.ffEquiv_algebraMap]
      rfl
    rw [hf_apply, hιR_apply, h1, h2, h3, h4, qexp_apply, h5, h6, coe_algebraMap_full]
  have hι' : ∀ r : R, e (ιR r) = PowerSeries.C (algebraMap R ℚ r) := by
    intro r
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [he', HahnSeries.ofPowerSeries_C, hconst]

  have hu' : e t = u.map (algebraMap R ℚ) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [he', hf_apply, hu]

  have hI' : ∀ i ∈ RingHom.ker π, PowerSeries.constantCoeff (e i) = 0 := by
    have hκt : (PowerSeries.constantCoeff.comp e) t = 0 := by
      rw [RingHom.comp_apply, hu', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hu0, map_zero]
    intro i hi
    exact RingHom.ker_le_ker_of_ker_le_span_sup_sq_of_map_eq_zero π (PowerSeries.constantCoeff.comp e) t hκt hcot hi

  have htm : t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π) (by simpa [RingHom.mem_ker] using ht)

  have hP' : e z = (a • P).map (algebraMap R ℚ) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [he', hf_apply, hP]
  have hPa : ∀ n : ℕ, PowerSeries.coeff n (a • P) ∈ Ideal.span {a} := fun n => by
    rw [PowerSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)

  have hmem : z ∈ (Ideal.span {a}).map ιR :=
    RingHom.mem_map_of_powerSeries_map_eq_of_forall_coeff_mem hinj ιR π hπ t ht hcot htm e hι' hI' u hu' hu1
      (Ideal.span {a}) z (a • P) hP' hPa
  rw [Ideal.map_span, Set.image_singleton] at hmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨b, by rw [← hb, mul_comm, hιR_apply]⟩

end QSatStalk
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.LaurentSeries"

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero.ModularCurve AlgebraicCurve IsLocalRing CuspForm"

theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))))
    (hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s)

    (π : X.presheaf.stalk (εinf.1.base s) →+* ↥(GaloisRep.ratLocalizedAt p))
    (hπι : ∀ r : ↥(GaloisRep.ratLocalizedAt p), π ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))) = r)
    (hπker : RingHom.ker (Scheme.Hom.stalkMap εinf.1 s).hom ≤ RingHom.ker π)
    (t : X.presheaf.stalk (εinf.1.base s)) (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (u : PowerSeries ↥(GaloisRep.ratLocalizedAt p))
    (hu : ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom t))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))
    (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u))
    (z : X.presheaf.stalk (εinf.1.base s)) (P : PowerSeries ↥(GaloisRep.ratLocalizedAt p))
    (hP : ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom z))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ ((((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) • P).map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) :
    ∃ z' : X.presheaf.stalk (εinf.1.base s),
      z = (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) * z' := by
  haveI : IsNoetherianRing ↥(GaloisRep.ratLocalizedAt p) := by
    haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
    infer_instance
  exact ModularCurve.QSatStalk.main N (R := ↥(GaloisRep.ratLocalizedAt p)) Subtype.val_injective c M₀
    (e₀ ≫ pullback.fst c _) (by rw [Category.assoc, pullback.condition, ← Category.assoc, he₀])
    x₀ hx₀ (εinf.1.base s) hspec π hπι t ht hcot u hu hu0 hu1 ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) z P hP

end S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_eq_germ_mul_of_ffEquiv_symm_stalkMap_stalkSpecializes_eq_ofPowerSeries_smul_cuspSection_of_ratCurveModel_compat_of_neZero (solution)

-- Prove2me | solution 1 for ModularCurve.iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/03f94a6b-ee8d-5047-8648-8376880e9dd9

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Two
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible
import Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
import Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
import Theorems.Thm_ModularCurve_exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
p2m_attr_erase "instance" "EtaleCohomologyLES.instAdditiveSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.instFullSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.constSchemeOpAdditive EtaleCohomologyLES.instFaithfulSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf AlgebraicGeometry.Scheme.instAdditiveSheafFppfSmallFppfTopologyAbFppfCohomologyFunctor EtaleCohomologyLES.idIsContinuousEtaleFppf EtaleCohomologyLES.constantSheafEtaleAdditive EtaleCohomologyLES.constantSheafFppfAdditive EtaleCohomologyLES.etaleTopologySubcanonical EtaleCohomologyLES.etaleSheavesIsGrothendieckAbelian"
p2m_attr_erase "simp" "FppfCohomologyLES.cohomologyDimensionShiftEquiv_apply EtaleCohomologyLES.sheafInclusionOfLe_obj_obj FppfCohomologyLES.homPostcompAddEquiv_apply EtaleCohomologyLES.fppfSheafToEtaleSheaf_obj_obj AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_inv_app_apply FppfCohomologyLES.homPostcompAddEquiv_symm_apply AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_hom_app_apply EtaleCohomologyLES.sheafInclusionOfLe_map_hom EtaleCohomologyLES.fppfSheafToEtaleSheaf_map_hom Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

noncomputable section

namespace OTCLASSDM

def abIsoOfAddEquiv {A B : Ab.{1}} (φ : A ≃+ B) : A ≅ B where
  hom := AddCommGrpCat.ofHom φ.toAddMonoidHom
  inv := AddCommGrpCat.ofHom φ.symm.toAddMonoidHom

theorem nonempty_iso_restriction_of_sectionsEquiv
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (enat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (M.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (e' : ∀ T : Scheme.{0},
      (X.1.obj (Opposite.op T)) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))))
    (enat' : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : X.1.obj (Opposite.op T')) (k : K),
      (Additive.toMul (e' T (X.1.map g.op s))) k
        = (Scheme.Γ.map g.op) ((Additive.toMul (e' T' s)) k)) :
    Nonempty (M.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) := by
  refine ⟨NatIso.ofComponents
    (fun U => abIsoOfAddEquiv ((e U.unop).trans (e' U.unop.left).symm)) ?_⟩
  intro U V f
  ext s

  apply (e' V.unop.left).injective
  show e' V.unop.left ((e' V.unop.left).symm (e V.unop (M.1.map f s)))
      = e' V.unop.left (X.1.map (f.unop.left).op ((e' U.unop.left).symm (e U.unop s)))
  rw [AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply (WithConv.equiv _).injective
  refine AlgHom.ext fun k => ?_
  have h1 := enat' (f.unop.left) ((e' U.unop.left).symm (e U.unop s)) k
  rw [AddEquiv.apply_symm_apply] at h1
  exact (enat f.unop s k).trans h1.symm

end OTCLASSDM

namespace OTCLASSDN

private theorem pi_single_zero_sq :
    (Pi.single 0 1 : Fin 2 → ℤ) * Pi.single 0 1 = Pi.single 0 1 := by
  ext i; fin_cases i <;> simp

private theorem pi_eq_of_single_zero (x : Fin 2 → ℤ) :
    x = (x 1) • 1 + (x 0 - x 1) • Pi.single 0 1 := by
  ext i; fin_cases i <;> simp

theorem natCard_algHom_pi_fin_two_eq_two (B : Type*) [CommRing B] [IsDomain B] :
    Nat.card ((Fin 2 → ℤ) →ₐ[ℤ] B) = 2 := by
  have hdet : ∀ φ : (Fin 2 → ℤ) →ₐ[ℤ] B, ∀ x, φ x = x 1 + (x 0 - x 1) * φ (Pi.single 0 1) := by
    intro φ x
    conv_lhs => rw [pi_eq_of_single_zero x, map_add, map_zsmul, map_zsmul, map_one]
    push_cast [zsmul_eq_mul]
    ring
  have hidem : ∀ φ : (Fin 2 → ℤ) →ₐ[ℤ] B, φ (Pi.single 0 1) = 0 ∨ φ (Pi.single 0 1) = 1 := by
    intro φ
    exact IsIdempotentElem.iff_eq_zero_or_one.mp (by rw [IsIdempotentElem, ← map_mul, pi_single_zero_sq])
  set χ : Fin 2 → ((Fin 2 → ℤ) →ₐ[ℤ] B) :=
    fun i => (Algebra.ofId ℤ B).comp (Pi.evalAlgHom ℤ (fun _ => ℤ) i) with hχ
  rw [Nat.card_eq_two_iff]
  refine ⟨χ 1, χ 0, ?_, ?_⟩
  · intro h
    have := congrArg (· (Pi.single (0 : Fin 2) (1 : ℤ))) (congrArg DFunLike.coe h)
    simp only [hχ, AlgHom.coe_comp, Function.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne one_ne_zero, map_one, map_zero] at this
    exact zero_ne_one this
  · ext φ
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, iff_true]
    rcases hidem φ with h0 | h1
    · left; ext x
      simp only [hdet φ x, h0, mul_zero, add_zero, hχ, AlgHom.coe_comp, Function.comp_apply,
        Pi.evalAlgHom_apply, eq_intCast]
    · right; ext x
      simp only [hdet φ x, h1, mul_one, hχ, AlgHom.coe_comp, Function.comp_apply,
        Pi.evalAlgHom_apply, eq_intCast]
      ring

theorem sq_eq_one_iff_char_two (F : Type*) [Field F] [CharP F 2] (x : F) :
    x ^ 2 = 1 ↔ x = 1 := by
  constructor
  · intro hx
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have : (x - 1) ^ 2 = 0 := by linear_combination hx + (1 - x) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · rintro rfl; ring

theorem natCard_algHom_monoidAlgebra_zmod_two_char_two_eq_one
    (F : Type*) [Field F] [CharP F 2] :
    Nat.card (MonoidAlgebra ℤ (Multiplicative (ZMod 2)) →ₐ[ℤ] F) = 1 := by
  have hsub : Subsingleton (Multiplicative (ZMod 2) →* F) := by
    refine ⟨fun φ ψ => MonoidHom.ext fun g => ?_⟩
    have hg2 : g ^ (2 : ℕ) = 1 := by
      have htoAdd : (2 : ℕ) • Multiplicative.toAdd g = 0 := by
        haveI : CharP (ZMod 2) 2 := ZMod.charP 2
        rw [two_nsmul]; exact CharTwo.add_self_eq_zero _
      rw [← ofAdd_toAdd g, ← ofAdd_nsmul, htoAdd, ofAdd_zero]
    have hφ : φ g = 1 := (sq_eq_one_iff_char_two F _).mp (by rw [← map_pow, hg2, map_one])
    have hψ : ψ g = 1 := (sq_eq_one_iff_char_two F _).mp (by rw [← map_pow, hg2, map_one])
    rw [hφ, hψ]
  rw [Nat.card_congr (MonoidAlgebra.lift ℤ F (Multiplicative (ZMod 2))).symm,
    Nat.card_eq_one_iff_unique]
  exact ⟨hsub, ⟨1⟩⟩

theorem pow_two_inj {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective le_rfl h

theorem natCard_algHom_congr_left {K K' : Type*} [CommSemiring K] [CommSemiring K']
    [Algebra ℤ K] [Algebra ℤ K'] (σ : K ≃ₐ[ℤ] K') (B : Type*) [CommSemiring B] [Algebra ℤ B] :
    Nat.card (K →ₐ[ℤ] B) = Nat.card (K' →ₐ[ℤ] B) :=
  Nat.card_congr (AlgEquiv.arrowCongr σ AlgEquiv.refl)

end OTCLASSDN

namespace OTCLASSDN3

theorem dichotomy (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Module.Flat ℤ K]
    (hfin : Module.Finite ℤ K)
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2) :
    Nonempty (K ≃ₐ[ℤ] (Fin 2 → ℤ)) ∨
      Nonempty (K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2))) := by
  have hmod : (Algebra.toModule : Module ℤ K) = AddCommGroup.toIntModule K := Subsingleton.elim _ _
  haveI := hfin
  haveI hfree : Module.Free ℤ K := inferInstance
  haveI hfinA : @Module.Finite ℤ K _ _ Algebra.toModule := by rw [hmod]; exact hfin
  haveI hfreeA : @Module.Free ℤ K _ _ Algebra.toModule := by rw [hmod]; exact hfree
  have hrank : @Module.finrank ℤ K _ _ Algebra.toModule = 2 := by
    have h := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ K (AlgebraicClosure ℚ)
    rw [hgen] at h
    exact h.symm
  exact HopfAlgebra.nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible
    Int.prime_two.irreducible K hrank

end OTCLASSDN3

theorem solution
    (p : ℕ)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (enat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (M.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (a : ℕ) (ha : Nat.card (K →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a) :
    (a = 1 ∧ Nonempty (M.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
        (FppfKummerSES.sheafULift.{0}.obj
          (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj)) ∨
    (a = 0 ∧ Nonempty (M.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
        (FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj)) ∨
    (∃ l1 : ℕ, Nat.card (fppfCohomology specInt M 1) = 2 ^ l1 ∧ l1 + a ≤ 1) := by
  by_cases hfin : Module.Finite ℤ K
  · rcases OTCLASSDN3.dichotomy K hfin hgen with hf | hf
    · obtain ⟨f⟩ := hf
      refine Or.inl ⟨?_, ?_⟩
      · refine OTCLASSDN.pow_two_inj ?_
        rw [← ha, OTCLASSDN.natCard_algHom_congr_left f, pow_one]
        convert OTCLASSDN.natCard_algHom_pi_fin_two_eq_two (AlgebraicClosure (ZMod 2)) <;> first | rfl | exact Subsingleton.elim _ _
      · obtain ⟨e', enat'⟩ :=
          AlgebraicGeometry.exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two K f
        exact OTCLASSDM.nonempty_iso_restriction_of_sectionsEquiv K M e enat _ e' enat'
    · obtain ⟨f⟩ := hf
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · refine OTCLASSDN.pow_two_inj ?_
        rw [← ha, OTCLASSDN.natCard_algHom_congr_left f.toAlgEquiv, pow_zero]
        convert OTCLASSDN.natCard_algHom_monoidAlgebra_zmod_two_char_two_eq_one
          (AlgebraicClosure (ZMod 2)) <;> first | rfl | exact Subsingleton.elim _ _
      · obtain ⟨e', enat'⟩ :=
          AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two K f
        exact OTCLASSDM.nonempty_iso_restriction_of_sectionsEquiv K M e enat _ e' enat'
  · exact Or.inr (Or.inr
      (ModularCurve.exists_natCard_fppfCohomology_one_of_not_finite_of_sectionsEquiv_algHom_two
        p K M e enat hff hgen a ha hfin))

end

end S_ModularCurve_iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
end P2MW
export P2MW.S_ModularCurve_iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two (solution)

-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9bf1cea4-116f-5eb4-9161-b28ea3416704

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
import Theorems.Thm_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
import Theorems.Thm_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
import Theorems.Thm_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open WithConv

universe u

namespace P2mAffineTorsionCount

section PointGroup

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

theorem equiv_one {W : Type*} [Monoid W] (e : W ≃ SchemeHomOver t f)
    (he : ∀ φ ψ : W, e (φ * ψ) = L.mul t (e φ) (e ψ)) : e 1 = L.one t := by
  have h1 : L.mul t (e 1) (e 1) = e 1 := by rw [← he, one_mul]
  calc e 1 = L.mul t (L.inv t (e 1)) (L.mul t (e 1) (e 1)) := by
          rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
    _ = L.one t := by rw [h1, L.inv_mul_cancel]

theorem equiv_pow {W : Type*} [Monoid W] (e : W ≃ SchemeHomOver t f)
    (he : ∀ φ ψ : W, e (φ * ψ) = L.mul t (e φ) (e ψ)) (n : ℕ) (φ : W) :
    e (φ ^ n) = L.nsmul t n (e φ) := by
  induction n with
  | zero => rw [pow_zero, L.nsmul_zero, equiv_one L t e he]
  | succ n ih => rw [pow_succ, he, ih, L.nsmul_succ]

def torsionEquiv {W : Type*} [Monoid W] (e : W ≃ SchemeHomOver t f)
    (he : ∀ φ ψ : W, e (φ * ψ) = L.mul t (e φ) (e ψ)) (n : ℕ) :
    {φ : W // φ ^ n = 1} ≃ {x : SchemeHomOver t f // L.IsTorsionPoint t n x} :=
  e.subtypeEquiv fun φ => by
    rw [L.isTorsionPoint_def, ← equiv_pow L t e he, ← equiv_one L t e he]
    exact e.injective.eq_iff.symm

theorem transport {t t' : T ⟶ Spec (CommRingCat.of k)} (htt : t = t') (n B : ℕ)
    (H : Finite {x : SchemeHomOver t f // L.IsTorsionPoint t n x} ∧
      Nat.card {x : SchemeHomOver t f // L.IsTorsionPoint t n x} ≤ B) :
    Finite {x : SchemeHomOver t' f // L.IsTorsionPoint t' n x} ∧
      Nat.card {x : SchemeHomOver t' f // L.IsTorsionPoint t' n x} ≤ B := by
  subst htt
  exact H

end PointGroup

section Hopf

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]

abbrev CharLat : Type u := Additive (GroupLike k H)

noncomputable def inclHom : Multiplicative (CharLat k H) →* H where
  toFun x := (Additive.toMul (Multiplicative.toAdd x) : GroupLike k H).val
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def res : AddMonoidAlgebra k (CharLat k H) →ₐ[k] H :=
  AddMonoidAlgebra.lift k H (CharLat k H) (inclHom k H)

variable {k H}

theorem res_single (g : GroupLike k H) (c : k) :
    res k H (AddMonoidAlgebra.single (Additive.ofMul g) c) = c • g.val := by
  rw [res, AddMonoidAlgebra.lift_single]
  rfl

theorem convMul_apply_of_isGroupLikeElem (φ ψ : WithConv (H →ₐ[k] k)) {g : H}
    (hg : IsGroupLikeElem k g) : (φ * ψ) g = φ g * ψ g := by
  rw [AlgHom.convMul_apply, hg.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul]

theorem convOne_apply_of_isGroupLikeElem {g : H} (hg : IsGroupLikeElem k g) :
    (1 : WithConv (H →ₐ[k] k)) g = 1 := by
  rw [AlgHom.convOne_apply, hg.counit_eq_one, map_one]

theorem convPow_apply_of_isGroupLikeElem (φ : WithConv (H →ₐ[k] k)) {g : H}
    (hg : IsGroupLikeElem k g) (n : ℕ) : (φ ^ n) g = (φ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_of_isGroupLikeElem hg]
  | succ n ih => rw [pow_succ, convMul_apply_of_isGroupLikeElem _ _ hg, ih, pow_succ]

noncomputable def resPt (φ : WithConv (H →ₐ[k] k)) :
    WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) :=
  toConv (φ.ofConv.comp (res k H))

theorem resPt_single (φ : WithConv (H →ₐ[k] k)) (g : GroupLike k H) :
    resPt φ (AddMonoidAlgebra.single (Additive.ofMul g) 1) = φ g.val := by
  change φ.ofConv (res k H (AddMonoidAlgebra.single (Additive.ofMul g) 1)) = _
  rw [res_single, one_smul]

theorem comul_single_one (g : GroupLike k H) :
    Coalgebra.comul (R := k) (AddMonoidAlgebra.single (Additive.ofMul g) (1 : k)) =
      AddMonoidAlgebra.single (Additive.ofMul g) (1 : k) ⊗ₜ[k]
        AddMonoidAlgebra.single (Additive.ofMul g) (1 : k) := by
  rw [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  rfl

theorem counit_single_one (g : GroupLike k H) :
    Coalgebra.counit (R := k) (AddMonoidAlgebra.single (Additive.ofMul g) (1 : k)) = 1 := by
  rw [AddMonoidAlgebra.counit_single]
  rfl

theorem resPt_mul (φ ψ : WithConv (H →ₐ[k] k)) : resPt (φ * ψ) = resPt φ * resPt ψ := by
  apply WithConv.ofConv_injective
  refine AddMonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
  change resPt (φ * ψ) (AddMonoidAlgebra.single a 1) = (resPt φ * resPt ψ) (AddMonoidAlgebra.single a 1)
  obtain ⟨g, rfl⟩ : ∃ g : GroupLike k H, Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [resPt_single, convMul_apply_of_isGroupLikeElem _ _ g.2, AlgHom.convMul_apply,
    comul_single_one, Algebra.TensorProduct.lift_tmul]
  change _ = resPt φ _ * resPt ψ _
  rw [resPt_single, resPt_single]

theorem resPt_one : resPt (1 : WithConv (H →ₐ[k] k)) = 1 := by
  apply WithConv.ofConv_injective
  refine AddMonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
  change resPt (1 : WithConv (H →ₐ[k] k)) (AddMonoidAlgebra.single a 1) =
    (1 : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k)) (AddMonoidAlgebra.single a 1)
  obtain ⟨g, rfl⟩ : ∃ g : GroupLike k H, Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [resPt_single, convOne_apply_of_isGroupLikeElem g.2, AlgHom.convOne_apply, counit_single_one,
    map_one]

theorem resPt_pow (φ : WithConv (H →ₐ[k] k)) (n : ℕ) : resPt (φ ^ n) = resPt φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resPt_one]
  | succ n ih => rw [pow_succ, resPt_mul, ih, pow_succ]

theorem eq_of_resPt_eq [IsAlgClosed k] [Coalgebra.IsCocomm k H] {m : ℕ} (hm : (m : k) ≠ 0)
    {φ ψ : WithConv (H →ₐ[k] k)} (hφ : φ ^ m = 1) (hψ : ψ ^ m = 1)
    (hres : resPt φ = resPt ψ) : φ = ψ := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [h0, Nat.cast_zero]) hm
    · exact h0
  let χ : WithConv (H →ₐ[k] k) := ψ * φ ^ (m - 1)
  have hχm : χ ^ m = 1 := by
    change (ψ * φ ^ (m - 1)) ^ m = 1
    rw [mul_pow, hψ, one_mul, ← pow_mul, mul_comm, pow_mul, hφ, one_pow]
  have hval : ∀ g : H, IsGroupLikeElem k g → φ g = ψ g := by
    intro g hg
    have := congrArg (fun χ => χ (AddMonoidAlgebra.single (Additive.ofMul (⟨g, hg⟩ : GroupLike k H)) 1))
      hres
    simpa only [resPt_single] using this
  have hχ1 : ∀ g : H, IsGroupLikeElem k g → χ g = 1 := by
    intro g hg
    change (ψ * φ ^ (m - 1)) g = 1
    rw [convMul_apply_of_isGroupLikeElem _ _ hg, convPow_apply_of_isGroupLikeElem _ hg, ← hval g hg,
      ← pow_succ', Nat.sub_add_cancel hm1, ← convPow_apply_of_isGroupLikeElem _ hg, hφ,
      convOne_apply_of_isGroupLikeElem hg]
  have hχ : χ = 1 :=
    HopfAlgebra.withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem k H χ m hm hχm hχ1
  calc φ = χ * φ := by rw [hχ, one_mul]
    _ = ψ * φ ^ (m - 1 + 1) := by
        change ψ * φ ^ (m - 1) * φ = _
        rw [pow_succ, mul_assoc]
    _ = ψ := by rw [Nat.sub_add_cancel hm1, hφ, mul_one]

theorem finite_and_natCard_le [IsAlgClosed k] [Coalgebra.IsCocomm k H]
    [ConnectedSpace (PrimeSpectrum H)] (h : ℕ)
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H))
    (m : ℕ) (hm : (m : k) ≠ 0) :
    Finite {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1} ∧
      Nat.card {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1} ≤ m ^ h := by
  obtain ⟨hfree, hfin, hrank⟩ :=
    HopfAlgebra.free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
      k H h hsm
  haveI := hfree
  haveI := hfin
  haveI : NeZero (m : k) := ⟨hm⟩
  haveI : NeZero m := NeZero.of_neZero_natCast k
  have hT := AddMonoidAlgebra.natCard_withConv_algHom_pow_eq_one k (CharLat k H) k m
  let ι : {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1} →
      {χ : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) // χ ^ m = 1} :=
    fun φ => ⟨resPt φ.1, by rw [← resPt_pow, φ.2, resPt_one]⟩
  have hι : Function.Injective ι := by
    intro φ ψ hφψ
    apply Subtype.ext
    exact eq_of_resPt_eq hm φ.2 ψ.2 (congrArg Subtype.val hφψ)
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hfinT : Finite {χ : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) // χ ^ m = 1} := by
    apply Nat.finite_of_card_ne_zero
    rw [hT]
    exact pow_ne_zero _ (NeZero.ne m)
  refine ⟨Finite.of_injective ι hι, ?_⟩
  calc Nat.card {φ : WithConv (H →ₐ[k] k) // φ ^ m = 1}
      ≤ Nat.card {χ : WithConv (AddMonoidAlgebra k (CharLat k H) →ₐ[k] k) // χ ^ m = 1} :=
        Nat.card_le_card_of_injective ι hι
    _ = m ^ Module.finrank ℤ (CharLat k H) := hT
    _ ≤ m ^ h := Nat.pow_le_pow_right hm1 hrank

end Hopf

section SchemeSide

variable (k : Type u) [Field k] {N : Scheme.{u}} (f : N ⟶ Spec (CommRingCat.of k))

theorem specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem connectedSpace_primeSpectrum_of_iso [ConnectedSpace N] (H : Type u) [CommRing H]
    (I : N ≅ Spec (CommRingCat.of H)) : ConnectedSpace (PrimeSpectrum H) := by
  let e := Scheme.homeoOfIso I
  exact e.surjective.connectedSpace e.continuous

theorem locally_isStandardSmoothOfRelativeDimension_of_algEquiv [IsAffine N] (h : ℕ)
    [SmoothOfRelativeDimension h f] (H : Type u) [CommRing H]
    (algN : Algebra k Γ(N, ⊤))
    (halg : algebraMap k Γ(N, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
    [Algebra k H] (iso : H ≃ₐ[k] Γ(N, ⊤)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H) := by
  have hP : RingHom.RespectsIso (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h)) :=
    RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  have H1 : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) f.appTop.hom :=
    HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension h) f inferInstance

  let e₁ : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
  have H2 : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h)
      (f.appTop.hom.comp e₁.toRingHom) := hP.2 _ e₁ H1

  let e₂ : Γ(N, ⊤) ≃+* H := iso.symm.toRingEquiv
  have H3 := hP.1 _ e₂ H2
  have heq : algebraMap k H = e₂.toRingHom.comp (f.appTop.hom.comp e₁.toRingHom) := by
    ext x
    change algebraMap k H x = iso.symm (f.appTop.hom (e₁ x))
    have h1 : algebraMap k H x = iso.symm (algebraMap k Γ(N, ⊤) x) := (iso.symm.commutes x).symm
    rw [h1, halg]
    rfl
  rw [heq]
  exact H3

end SchemeSide

end P2mAffineTorsionCount

open P2mAffineTorsionCount

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}} [IsAffine N] [ConnectedSpace N]
    (f : N ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (h : ℕ) [SmoothOfRelativeDimension h f] (m : ℕ) (hm : (m : k) ≠ 0) :
    Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ∧
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≤ m ^ h := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth h f
  haveI : LocallyOfFiniteType f := inferInstance

  letI algN : Algebra k Γ(N, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
  obtain ⟨H, _instR, _instH, hft, hfl, hcocomm, iso, e, hept, hemul, henat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
      L (fun t x y => hc t x y)
  haveI := hcocomm

  haveI : ConnectedSpace (PrimeSpectrum H) := by
    refine connectedSpace_primeSpectrum_of_iso (N := N) H (N.isoSpec ≪≫ ?_)
    exact Scheme.Spec.mapIso (iso.toRingEquiv.toCommRingCatIso).op
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H) :=
    locally_isStandardSmoothOfRelativeDimension_of_algEquiv k f h H algN rfl iso

  obtain ⟨hfinH, hcardH⟩ := finite_and_natCard_le (k := k) (H := H) h hsm m hm

  apply transport L (specMap_algebraMap_self k) m (m ^ h)
  let E := torsionEquiv L _ (e k) (hemul k) m
  exact ⟨Finite.of_equiv _ E, by rw [← Nat.card_congr E]; exact hcardH⟩

end S_GoodReductionJacobian_RelativeGroupLaw_finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finite_and_natCard_isTorsionPoint_le_pow_of_isAffine (solution)

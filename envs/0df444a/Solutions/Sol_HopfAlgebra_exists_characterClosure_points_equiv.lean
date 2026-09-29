-- Prove2me | solution 1 for HopfAlgebra.exists_characterClosure_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f76eca1f-c6b8-5b30-a16f-6af2fcd20942

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FiniteFlat_ClosureHopfAlgebra
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective
import Theorems.Thm_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv

set_option autoImplicit false

open scoped TensorProduct
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

section P13_T5_FIELD

set_option autoImplicit false

namespace P2MMultE

open scoped TensorProduct

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A]
variable {L : Type*} [CommRing L] [Algebra F L]

abbrev vanishingIdeal (S : Set (A →ₐ[F] L)) : Ideal A := HopfAlgebra.vanishingIdealOfPoints S

theorem mem_vanishingIdeal_iff (S : Set (A →ₐ[F] L)) (a : A) :
    a ∈ vanishingIdeal S ↔ ∀ ν ∈ S, ν a = 0 := Iff.rfl

theorem vanishingIdeal_antitone {S T : Set (A →ₐ[F] L)} (h : S ⊆ T) :
    vanishingIdeal T ≤ vanishingIdeal S := fun _ ha ν hν => ha ν (h hν)

noncomputable def convPt (ν ν' : A →ₐ[F] L) : A →ₐ[F] L :=
  (Algebra.TensorProduct.lmul' F (S := L)).comp
    ((Algebra.TensorProduct.map ν ν').comp (Bialgebra.comulAlgHom F A))

noncomputable def onePt : A →ₐ[F] L := (Algebra.ofId F L).comp (Bialgebra.counitAlgHom F A)

structure IsPtSubgroup (S : Set (A →ₐ[F] L)) : Prop where
  one_mem : onePt ∈ S
  mul_mem : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S
  inv_mem : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)

theorem onePt_apply (a : A) : (onePt : A →ₐ[F] L) a = algebraMap F L (Coalgebra.counit (R := F) a) := rfl

theorem convPt_apply (ν ν' : A →ₐ[F] L) (a : A) :
    convPt ν ν' a = Algebra.TensorProduct.lmul' F (S := L)
      (Algebra.TensorProduct.map ν ν' (Coalgebra.comul (R := F) a)) := rfl

theorem counit_eq_zero_of_mem_vanishingIdeal {S : Set (A →ₐ[F] L)} (hS : onePt ∈ S)
    [FaithfulSMul F L] {a : A} (ha : a ∈ vanishingIdeal S) : Coalgebra.counit (R := F) a = 0 := by
  have h := ha onePt hS
  rw [onePt_apply] at h
  exact (FaithfulSMul.algebraMap_injective F L) (by rw [h, map_zero])

noncomputable abbrev liftPt (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) :
    (A ⧸ vanishingIdeal S) →ₐ[F] L :=
  HopfAlgebra.liftPoint S ν hν

theorem liftPt_mk (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) (a : A) :
    liftPt S ν hν (Ideal.Quotient.mk (vanishingIdeal S) a) = ν a := rfl

private noncomputable abbrev _root_.P2MMultE.evalPair (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) :
    (A ⧸ vanishingIdeal S) ⊗[F] (A ⧸ vanishingIdeal S) →ₐ[F] L :=
  HopfAlgebra.evalPair S ν ν' hν hν'

p2m_export "P2MMultE" "evalPair"
theorem evalPair_map_mk (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S)
    (x : A ⊗[F] A) :
    evalPair S ν ν' hν hν' (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal S))
      (Ideal.Quotient.mkₐ F (vanishingIdeal S)) x)
      = Algebra.TensorProduct.lmul' F (S := L) (Algebra.TensorProduct.map ν ν' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [evalPair, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
      Ideal.Quotient.mkₐ_eq_mk]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem evalPair_map_comul_eq_zero {S : Set (A →ₐ[F] L)}
    (hS : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S)
    {a : A} (ha : a ∈ vanishingIdeal S) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) :
    evalPair S ν ν' hν hν' (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal S))
      (Ideal.Quotient.mkₐ F (vanishingIdeal S)) (Coalgebra.comul (R := F) a)) = 0 := by
  rw [evalPair_map_mk, ← convPt_apply]
  exact ha _ (hS ν ν' hν hν')

theorem map_mk_comul_eq_zero {S : Set (A →ₐ[F] L)}
    (hS : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S)
    (hsep : ∀ x : (A ⧸ vanishingIdeal S) ⊗[F] (A ⧸ vanishingIdeal S),
      (∀ ν ν' (hν : ν ∈ S) (hν' : ν' ∈ S), evalPair S ν ν' hν hν' x = 0) → x = 0)
    {a : A} (ha : a ∈ vanishingIdeal S) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal S))
      (Ideal.Quotient.mkₐ F (vanishingIdeal S)) (Coalgebra.comul (R := F) a) = 0 :=
  hsep _ fun ν ν' hν hν' => evalPair_map_comul_eq_zero hS ha ν ν' hν hν'

theorem antipode_mem_vanishingIdeal {S : Set (A →ₐ[F] L)}
    (hS : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    {a : A} (ha : a ∈ vanishingIdeal S) : HopfAlgebraStruct.antipode (R := F) a ∈ vanishingIdeal S := by
  intro ν hν
  obtain ⟨ν', hν', h⟩ := hS ν hν
  have := LinearMap.congr_fun h a
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [← this]
  exact ha ν' hν'

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section CharSub

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [CommRing L] [Algebra F L]

noncomputable def liftFun (I : Ideal A) (θ : Module.Dual F A) (hθ : ∀ a ∈ I, θ a = 0) :
    Module.Dual F (A ⧸ I) :=
  (I.restrictScalars F).liftQ θ (fun a ha => (LinearMap.mem_ker).2 (hθ a ha))

theorem liftFun_mk (I : Ideal A) (θ : Module.Dual F A) (hθ : ∀ a ∈ I, θ a = 0) (a : A) :
    liftFun I θ hθ (Ideal.Quotient.mk I a) = θ a := rfl

theorem dualDistrib_tmul_eq_comp_map (I : Ideal A) (θ θ' : Module.Dual F A)
    (hθ : ∀ a ∈ I, θ a = 0) (hθ' : ∀ a ∈ I, θ' a = 0) (x : A ⊗[F] A) :
    TensorProduct.dualDistrib F A A (θ ⊗ₜ[F] θ') x
      = TensorProduct.dualDistrib F (A ⧸ I) (A ⧸ I) (liftFun I θ hθ ⊗ₜ[F] liftFun I θ' hθ')
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [TensorProduct.dualDistrib_apply, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [FaithfulSMul F L]

noncomputable def charSub (S : Set (A →ₐ[F] L)) (hS1 : onePt ∈ S)
    (hSmul : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S)
    (hsep : ∀ x : (A ⧸ vanishingIdeal S) ⊗[F] (A ⧸ vanishingIdeal S),
      (∀ ν ν' (hν : ν ∈ S) (hν' : ν' ∈ S), evalPair S ν ν' hν hν' x = 0) → x = 0) :
    Subalgebra F (CartierDual F A) where
  carrier := {θ | ∀ a ∈ vanishingIdeal S, θ a = 0}
  mul_mem' {θ θ'} hθ hθ' := by
    intro a ha
    rw [CartierDual.mul_apply, dualDistrib_tmul_eq_comp_map (vanishingIdeal S) (CartierDual.toDual F A θ)
      (CartierDual.toDual F A θ') hθ hθ', map_mk_comul_eq_zero hSmul hsep ha, map_zero]
  one_mem' := by
    intro a ha
    rw [CartierDual.one_apply]
    exact counit_eq_zero_of_mem_vanishingIdeal hS1 ha
  add_mem' {θ θ'} hθ hθ' := fun a ha => by
    show θ a + θ' a = 0
    rw [hθ a ha, hθ' a ha, add_zero]
  zero_mem' := fun a _ => rfl
  algebraMap_mem' c := by
    intro a ha
    rw [CartierDual.algebraMap_apply, counit_eq_zero_of_mem_vanishingIdeal hS1 ha, zero_mul]

theorem mem_charSub_iff {S : Set (A →ₐ[F] L)} {hS1 hSmul hsep} {θ : CartierDual F A} :
    θ ∈ charSub S hS1 hSmul hsep ↔ ∀ a ∈ vanishingIdeal S, θ a = 0 := Iff.rfl

theorem comp_antipode_mem_charSub {S : Set (A →ₐ[F] L)} {hS1 hSmul hsep}
    (hSinv : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    {θ : CartierDual F A} (hθ : θ ∈ charSub S hS1 hSmul hsep) (a : A) (ha : a ∈ vanishingIdeal S) :
    θ (HopfAlgebraStruct.antipode (R := F) a) = 0 :=
  hθ _ (antipode_mem_vanishingIdeal hSinv ha)

end CharSub

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section AlgIso

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]

private abbrev _root_.P2MMultE.ptSet (S : Submonoid (WithConv (A →ₐ[F] L))) : Set (A →ₐ[F] L) := HopfAlgebra.ptSet S

p2m_export "P2MMultE" "ptSet"
theorem mem_ptSet {S : Submonoid (WithConv (A →ₐ[F] L))} (ν : ↥S) : WithConv.ofConv ν.1 ∈ ptSet S := by
  show WithConv.toConv (WithConv.ofConv ν.1) ∈ S
  simpa using ν.2

abbrev QS (S : Submonoid (WithConv (A →ₐ[F] L))) : Type _ := HopfAlgebra.pointQuot S

noncomputable abbrev evQ (S : Submonoid (WithConv (A →ₐ[F] L))) :
    L ⊗[F] QS S →ₐ[L] (↥S → L) :=
  HopfAlgebra.evalQuot S

theorem evQ_tmul (S : Submonoid (WithConv (A →ₐ[F] L))) (c : L) (a : A) (ν : ↥S) :
    evQ S (c ⊗ₜ[F] Ideal.Quotient.mk _ a) ν = c * (WithConv.ofConv ν.1) a :=
  HopfAlgebra.evalQuot_tmul S c a ν

noncomputable def ptL (ν : A →ₐ[F] L) : L ⊗[F] A →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) ν (fun _ _ => Commute.all _ _)

theorem ptL_tmul (ν : A →ₐ[F] L) (c : L) (a : A) : ptL ν (c ⊗ₜ[F] a) = c * ν a := by
  simp only [ptL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem evQ_map_mk (S : Submonoid (WithConv (A →ₐ[F] L))) (x : L ⊗[F] A) (ν : ↥S) :
    evQ S (Algebra.TensorProduct.map (AlgHom.id L L) (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S))) x) ν
      = ptL (WithConv.ofConv ν.1) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, evQ_tmul, ptL_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem ptL_conv (ν ν' : A →ₐ[F] L) (x : L ⊗[F] A) :
    ptL (convPt ν ν') x
      = Algebra.TensorProduct.lmul' L (S := L)
          (Algebra.TensorProduct.map (ptL ν) (ptL ν') (Coalgebra.comul (R := L) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    rw [ptL_tmul, convPt_apply, TensorProduct.comul_tmul]
    have hc : Coalgebra.comul (R := L) c = (1 : L) ⊗ₜ[L] c := by simp
    rw [hc]
    induction (Coalgebra.comul (R := F) a) using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, mul_zero]
    | tmul a₁ a₂ =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, ptL_tmul, ptL_tmul]
      ring
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, mul_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgIso

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section QuotCoalg

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]

structure PtHyp (S : Submonoid (WithConv (A →ₐ[F] L))) : Prop where
  one_mem : onePt ∈ ptSet S
  mul_mem : ∀ ν ν', ν ∈ ptSet S → ν' ∈ ptSet S → convPt ν ν' ∈ ptSet S
  sep : ∀ x : QS S ⊗[F] QS S,
    (∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0

theorem ofConv_mul (x y : WithConv (A →ₐ[F] L)) :
    WithConv.ofConv (x * y) = convPt (WithConv.ofConv x) (WithConv.ofConv y) := rfl

theorem PtHyp.of_isPtSubgroup {S : Submonoid (WithConv (A →ₐ[F] L))}
    (hsep : ∀ x : QS S ⊗[F] QS S,
      (∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0) :
    PtHyp S where
  one_mem := by
    show WithConv.toConv onePt ∈ S
    have : (WithConv.toConv (onePt : A →ₐ[F] L)) = 1 := rfl
    rw [this]; exact S.one_mem
  mul_mem := by
    intro ν ν' hν hν'
    show WithConv.toConv (convPt ν ν') ∈ S
    have : WithConv.toConv (convPt ν ν') = WithConv.toConv ν * WithConv.toConv ν' := rfl
    rw [this]; exact S.mul_mem hν hν'
  sep := hsep

variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def comulQ (h : PtHyp S) : QS S →ₗ[F] QS S ⊗[F] QS S :=
  ((vanishingIdeal (ptSet S)).restrictScalars F).liftQ
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S)))
        (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S)))).toLinearMap ∘ₗ Coalgebra.comul (R := F) (A := A))
    (by
      intro a ha
      rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
      exact map_mk_comul_eq_zero h.mul_mem h.sep ha)

theorem comulQ_mk (h : PtHyp S) (a : A) :
    comulQ h (Ideal.Quotient.mk _ a)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S)))
          (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S))) (Coalgebra.comul (R := F) a) := rfl

noncomputable def ptQ (ν : ↥S) : QS S →ₐ[F] L := liftPt (ptSet S) (WithConv.ofConv ν.1) (mem_ptSet ν)

theorem ptQ_mk (ν : ↥S) (a : A) : ptQ ν (Ideal.Quotient.mk _ a) = (WithConv.ofConv ν.1) a := rfl

theorem ptQ_mul (h : PtHyp S) (ν ν' : ↥S) (q : QS S) :
    ptQ (ν * ν') q = LinearMap.mul' F L (TensorProduct.map (ptQ ν).toLinearMap (ptQ ν').toLinearMap (comulQ h q)) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [ptQ_mk, Submonoid.coe_mul, ofConv_mul, convPt_apply, comulQ_mk]
  induction (Coalgebra.comul (R := F) a) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a₁ a₂ =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def counitQ (h : PtHyp S) : QS S →ₗ[F] F :=
  ((vanishingIdeal (ptSet S)).restrictScalars F).liftQ (Coalgebra.counit (R := F) (A := A))
    (by intro a ha; rw [LinearMap.mem_ker]; exact counit_eq_zero_of_mem_vanishingIdeal h.one_mem ha)

theorem counitQ_mk (h : PtHyp S) (a : A) : counitQ h (Ideal.Quotient.mk _ a) = Coalgebra.counit (R := F) a := rfl

theorem ptQ_one (h : PtHyp S) (q : QS S) : ptQ (1 : ↥S) q = algebraMap F L (counitQ h q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [ptQ_mk, counitQ_mk]
  rfl

end QuotCoalg

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section LLevel

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def ptQL (ν : ↥S) : L ⊗[F] QS S →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) (ptQ ν) (fun _ _ => Commute.all _ _)

theorem ptQL_tmul (ν : ↥S) (c : L) (q : QS S) : ptQL ν (c ⊗ₜ[F] q) = c * ptQ ν q := by
  simp only [ptQL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem evQ_eq_ptQL (x : L ⊗[F] QS S) (ν : ↥S) : evQ S x ν = ptQL ν x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul c q =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [evQ_tmul, ptQL_tmul, ptQ_mk]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

noncomputable def comulQL (h : PtHyp S) :
    L ⊗[F] QS S →ₗ[L] (L ⊗[F] QS S) ⊗[L] (L ⊗[F] QS S) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S)).toLinearMap
    ∘ₗ (comulQ h).baseChange L

theorem comulQL_tmul (h : PtHyp S) (c : L) (q : QS S) :
    comulQL h (c ⊗ₜ[F] q)
      = TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S) (c ⊗ₜ[F] comulQ h q) := by
  simp only [comulQL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul]

theorem mul'_map_ptQL_distribBaseChange (ν ν' : ↥S) (c : L) (t : QS S ⊗[F] QS S) :
    LinearMap.mul' L L (TensorProduct.map (ptQL ν).toLinearMap (ptQL ν').toLinearMap
      (TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S) (c ⊗ₜ[F] t)))
      = c * LinearMap.mul' F L (TensorProduct.map (ptQ ν).toLinearMap (ptQ ν').toLinearMap t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, mul_zero]
  | tmul q₁ q₂ =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    simp only [AlgHom.toLinearMap_apply, ptQL_tmul, one_mul]
    ring
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]

theorem ptQL_mul (h : PtHyp S) (ν ν' : ↥S) (x : L ⊗[F] QS S) :
    ptQL (ν * ν') x
      = LinearMap.mul' L L (TensorProduct.map (ptQL ν).toLinearMap (ptQL ν').toLinearMap (comulQL h x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c q => rw [ptQL_tmul, ptQ_mul h, comulQL_tmul, mul'_map_ptQL_distribBaseChange]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ptQL_one (h : PtHyp S) (c : L) (q : QS S) :
    ptQL (1 : ↥S) (c ⊗ₜ[F] q) = c * algebraMap F L (counitQ h q) := by
  rw [ptQL_tmul, ptQ_one h]

end LLevel

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section DualSide

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable abbrev CSub (h : PtHyp S) : Subalgebra F (CartierDual F A) :=
  charSub (ptSet S) h.one_mem h.mul_mem h.sep

noncomputable def toDualQ (h : PtHyp S) : ↥(CSub h) →ₗ[F] Module.Dual F (QS S) where
  toFun θ := liftFun (vanishingIdeal (ptSet S)) (CartierDual.toDual F A θ.1) θ.2
  map_add' θ θ' := by
    apply LinearMap.ext; intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  map_smul' c θ := by
    apply LinearMap.ext; intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl

theorem toDualQ_mk (h : PtHyp S) (θ : ↥(CSub h)) (a : A) :
    toDualQ h θ (Ideal.Quotient.mk _ a) = θ.1 a := rfl

theorem toDualQ_injective (h : PtHyp S) : Function.Injective (toDualQ h) := by
  intro θ θ' hθ
  apply Subtype.ext
  apply CartierDual.ext
  intro a
  have := LinearMap.congr_fun hθ (Ideal.Quotient.mk _ a)
  exact this

theorem toDualQ_surjective (h : PtHyp S) : Function.Surjective (toDualQ h) := by
  intro φ
  refine ⟨⟨CartierDual.ofDual F A (φ ∘ₗ ((vanishingIdeal (ptSet S)).restrictScalars F).mkQ), ?_⟩, ?_⟩
  · intro a ha
    have h0 : ((vanishingIdeal (ptSet S)).restrictScalars F).mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    show φ (((vanishingIdeal (ptSet S)).restrictScalars F).mkQ a) = 0
    rw [h0]
    exact map_zero φ
  · apply LinearMap.ext; intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl

theorem toDualQ_mul (h : PtHyp S) (θ θ' : ↥(CSub h)) (q : QS S) :
    toDualQ h (θ * θ') q
      = TensorProduct.dualDistrib F (QS S) (QS S) (toDualQ h θ ⊗ₜ[F] toDualQ h θ') (comulQ h q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [toDualQ_mk, Subalgebra.coe_mul, CartierDual.mul_apply, comulQ_mk,
    dualDistrib_tmul_eq_comp_map (vanishingIdeal (ptSet S)) (CartierDual.toDual F A θ.1)
      (CartierDual.toDual F A θ'.1) θ.2 θ'.2]
  rfl

theorem toDualQ_one (h : PtHyp S) (q : QS S) : toDualQ h 1 q = counitQ h q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [toDualQ_mk, Subalgebra.coe_one, CartierDual.one_apply, counitQ_mk]

noncomputable def dualBC : L ⊗[F] Module.Dual F (QS S) →ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.ringLmapEquivSelf L L (Module.Dual F (QS S) →ₗ[F] Module.Dual L (L ⊗[F] QS S))).symm
      (Module.Dual.baseChange L))

theorem dualBC_tmul_tmul (c : L) (φ : Module.Dual F (QS S)) (c' : L) (q : QS S) :
    dualBC (S := S) (c ⊗ₜ[F] φ) (c' ⊗ₜ[F] q) = c * (c' * algebraMap F L (φ q)) := by
  have h1 : dualBC (S := S) (c ⊗ₜ[F] φ) = c • Module.Dual.baseChange L φ := by
    simp [dualBC, LinearMap.ringLmapEquivSelf_symm_apply]
  rw [h1, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  simp [Module.Dual.baseChange, Algebra.smul_def, mul_comm]

end DualSide

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section Theta

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def Θ (h : PtHyp S) : L ⊗[F] ↥(CSub h) →ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  dualBC ∘ₗ (toDualQ h).baseChange L

theorem Θ_tmul_tmul (h : PtHyp S) (c : L) (θ : ↥(CSub h)) (c' : L) (q : QS S) :
    Θ h (c ⊗ₜ[F] θ) (c' ⊗ₜ[F] q) = c * (c' * algebraMap F L (toDualQ h θ q)) := by
  simp only [Θ, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, dualBC_tmul_tmul]

noncomputable def pairQ (f g : Module.Dual L (L ⊗[F] QS S)) : QS S ⊗[F] QS S →ₗ[F] L :=
  TensorProduct.lift
    (LinearMap.mk₂ F (fun q₁ q₂ => f ((1 : L) ⊗ₜ[F] q₁) * g ((1 : L) ⊗ₜ[F] q₂))
      (fun q q' q₂ => by simp only [TensorProduct.tmul_add, map_add, add_mul])
      (fun c q q₂ => by simp only [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, smul_mul_assoc])
      (fun q q₂ q₂' => by simp only [TensorProduct.tmul_add, map_add, mul_add])
      (fun c q q₂ => by simp only [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, mul_smul_comm]))

theorem pairQ_tmul (f g : Module.Dual L (L ⊗[F] QS S)) (q₁ q₂ : QS S) :
    pairQ f g (q₁ ⊗ₜ[F] q₂) = f ((1 : L) ⊗ₜ[F] q₁) * g ((1 : L) ⊗ₜ[F] q₂) := rfl

theorem mul'_map_distribBaseChange (f g : Module.Dual L (L ⊗[F] QS S)) (c : L) (t : QS S ⊗[F] QS S) :
    LinearMap.mul' L L (TensorProduct.map f g
      (TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S) (c ⊗ₜ[F] t)))
      = c * pairQ f g t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, mul_zero]
  | tmul q₁ q₂ =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      pairQ_tmul]
    have : f (c ⊗ₜ[F] q₁) = c * f ((1 : L) ⊗ₜ[F] q₁) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, mul_assoc]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]

theorem pairQ_Θ_tmul (h : PtHyp S) (c c' : L) (θ θ' : ↥(CSub h)) (t : QS S ⊗[F] QS S) :
    pairQ (Θ h (c ⊗ₜ[F] θ)) (Θ h (c' ⊗ₜ[F] θ')) t
      = c * c' * algebraMap F L (TensorProduct.dualDistrib F (QS S) (QS S) (toDualQ h θ ⊗ₜ[F] toDualQ h θ') t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul q₁ q₂ =>
    rw [pairQ_tmul, Θ_tmul_tmul, Θ_tmul_tmul, TensorProduct.dualDistrib_apply, map_mul]
    ring
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

theorem Θ_mul (h : PtHyp S) (w w' : L ⊗[F] ↥(CSub h)) (x : L ⊗[F] QS S) :
    Θ h (w * w') x = LinearMap.mul' L L (TensorProduct.map (Θ h w) (Θ h w') (comulQL h x)) := by
  induction w using TensorProduct.induction_on generalizing x with
  | zero => simp only [zero_mul, map_zero, LinearMap.zero_apply, TensorProduct.map_zero_left]
  | tmul c θ =>
    induction w' using TensorProduct.induction_on generalizing x with
    | zero => simp only [mul_zero, map_zero, LinearMap.zero_apply, TensorProduct.map_zero_right]
    | tmul c' θ' =>
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c'' q =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, Θ_tmul_tmul, toDualQ_mul, comulQL_tmul,
          mul'_map_distribBaseChange, pairQ_Θ_tmul]
        ring
      | add x y hx hy => simp only [map_add, hx, hy]
    | add u v hu hv => simp only [mul_add, map_add, LinearMap.add_apply, TensorProduct.map_add_right, hu, hv]
  | add u v hu hv =>
    simp only [add_mul, map_add, LinearMap.add_apply, TensorProduct.map_add_left, hu, hv]

end Theta

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section Bij

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

theorem dualBC_bijective : Function.Bijective (dualBC (S := S) (F := F) (L := L)) := by
  classical
  let bQ := Module.finBasis F (QS S)
  let b₁ := Algebra.TensorProduct.basis L bQ.dualBasis
  let b₂ := (Algebra.TensorProduct.basis L bQ).dualBasis
  have key : dualBC (S := S) = (b₁.equiv b₂ (Equiv.refl _)).toLinearMap := by
    refine b₁.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    refine (Algebra.TensorProduct.basis L bQ).ext fun j => ?_
    rw [Module.Basis.dualBasis_apply_self, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      dualBC_tmul_tmul, Module.Basis.dualBasis_apply_self]
    split_ifs <;> simp
  rw [key]
  exact (b₁.equiv b₂ (Equiv.refl _)).bijective

noncomputable def toDualQEquiv (h : PtHyp S) : ↥(CSub h) ≃ₗ[F] Module.Dual F (QS S) :=
  LinearEquiv.ofBijective (toDualQ h) ⟨toDualQ_injective h, toDualQ_surjective h⟩

theorem Θ_bijective (h : PtHyp S) : Function.Bijective (Θ h) := by
  have h1 : Function.Bijective ((toDualQ h).baseChange L) := by
    have : (toDualQ h).baseChange L = ((toDualQEquiv h).baseChange F L _ _).toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c θ
      rfl
    rw [this]; exact LinearEquiv.bijective _
  exact dualBC_bijective.comp h1

noncomputable def ΘEquiv (h : PtHyp S) : L ⊗[F] ↥(CSub h) ≃ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  LinearEquiv.ofBijective (Θ h) (Θ_bijective h)

theorem ΘEquiv_apply (h : PtHyp S) (w : L ⊗[F] ↥(CSub h)) : ΘEquiv h w = Θ h w := rfl

theorem Θ_one (h : PtHyp S) : Θ h 1 = (ptQL (1 : ↥S)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c q
  rw [Algebra.TensorProduct.one_def, Θ_tmul_tmul, one_mul, AlgHom.toLinearMap_apply, ptQL_one h, toDualQ_one]

noncomputable def dElt (h : PtHyp S) (ν : ↥S) : L ⊗[F] ↥(CSub h) := (ΘEquiv h).symm (ptQL ν).toLinearMap

theorem Θ_dElt (h : PtHyp S) (ν : ↥S) : Θ h (dElt h ν) = (ptQL ν).toLinearMap := by
  rw [dElt, ← ΘEquiv_apply, LinearEquiv.apply_symm_apply]

noncomputable def dHom (h : PtHyp S) : ↥S →* L ⊗[F] ↥(CSub h) where
  toFun := dElt h
  map_one' := by
    apply (ΘEquiv h).injective
    rw [ΘEquiv_apply, ΘEquiv_apply, Θ_dElt, Θ_one]
  map_mul' ν ν' := by
    apply (ΘEquiv h).injective
    rw [ΘEquiv_apply, ΘEquiv_apply, Θ_dElt]
    apply LinearMap.ext; intro x
    rw [Θ_mul, Θ_dElt, Θ_dElt, AlgHom.toLinearMap_apply, ptQL_mul h]

theorem dHom_apply (h : PtHyp S) (ν : ↥S) : dHom h ν = dElt h ν := rfl

noncomputable def ΨHom (h : PtHyp S) : MonoidAlgebra L ↥S →ₐ[L] L ⊗[F] ↥(CSub h) :=
  MonoidAlgebra.lift L _ ↥S (dHom h)

theorem ΨHom_single (h : PtHyp S) (ν : ↥S) (c : L) : ΨHom h (MonoidAlgebra.single ν c) = c • dElt h ν := by
  rw [ΨHom, MonoidAlgebra.lift_single, dHom_apply]

end Bij

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section Points

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def evQEquiv (hev : Function.Bijective (evQ S)) : L ⊗[F] QS S ≃ₐ[L] (↥S → L) :=
  AlgEquiv.ofBijective (evQ S) hev

noncomputable def evalBasis [Finite ↥S] (hev : Function.Bijective (evQ S)) :
    Module.Basis ↥S L (Module.Dual L (L ⊗[F] QS S)) := by
  classical
  exact (Pi.basisFun L ↥S).dualBasis.map (evQEquiv hev).toLinearEquiv.dualMap

theorem evalBasis_apply [Finite ↥S] (hev : Function.Bijective (evQ S)) (ν : ↥S) :
    evalBasis hev ν = (ptQL ν).toLinearMap := by
  classical
  apply LinearMap.ext; intro x
  simp only [evalBasis, Module.Basis.map_apply, LinearEquiv.dualMap_apply, Module.Basis.dualBasis_apply,
    Pi.basisFun_repr, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply]
  rw [← evQ_eq_ptQL]
  rfl

noncomputable def dBasis [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    Module.Basis ↥S L (L ⊗[F] ↥(CSub h)) :=
  (evalBasis hev).map (ΘEquiv h).symm

theorem dBasis_apply [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) (ν : ↥S) :
    dBasis h hev ν = dElt h ν := by
  rw [dBasis, Module.Basis.map_apply, evalBasis_apply]; rfl

theorem ΨHom_bijective [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    Function.Bijective (ΨHom h) := by
  classical
  let b₁ : Module.Basis ↥S L (MonoidAlgebra L ↥S) := MonoidAlgebra.basis ↥S L
  have key : (ΨHom h).toLinearMap = (b₁.equiv (dBasis h hev) (Equiv.refl _)).toLinearMap := by
    refine b₁.ext fun ν => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, dBasis_apply, AlgHom.toLinearMap_apply]
    rw [MonoidAlgebra.basis_apply]
    have := ΨHom_single h ν 1
    rw [one_smul] at this
    exact this
  have : Function.Bijective (ΨHom h).toLinearMap := by rw [key]; exact LinearEquiv.bijective _
  exact this

noncomputable def Ψ [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    MonoidAlgebra L ↥S ≃ₐ[L] L ⊗[F] ↥(CSub h) :=
  AlgEquiv.ofBijective (ΨHom h) (ΨHom_bijective h hev)

theorem Ψ_single [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) (ν : ↥S) (c : L) :
    Ψ h hev (MonoidAlgebra.single ν c) = c • dElt h ν := ΨHom_single h ν c

noncomputable def extL (h : PtHyp S) (Φ : ↥(CSub h) →ₐ[F] L) : L ⊗[F] ↥(CSub h) →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) Φ (fun _ _ => Commute.all _ _)

theorem extL_tmul (h : PtHyp S) (Φ : ↥(CSub h) →ₐ[F] L) (c : L) (θ : ↥(CSub h)) :
    extL h Φ (c ⊗ₜ[F] θ) = c * Φ θ := by
  simp only [extL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]

noncomputable def resF (h : PtHyp S) (Φ' : L ⊗[F] ↥(CSub h) →ₐ[L] L) : ↥(CSub h) →ₐ[F] L :=
  (Φ'.restrictScalars F).comp Algebra.TensorProduct.includeRight

theorem resF_apply (h : PtHyp S) (Φ' : L ⊗[F] ↥(CSub h) →ₐ[L] L) (θ : ↥(CSub h)) :
    resF h Φ' θ = Φ' ((1 : L) ⊗ₜ[F] θ) := rfl

noncomputable def extEquiv (h : PtHyp S) : (↥(CSub h) →ₐ[F] L) ≃ (L ⊗[F] ↥(CSub h) →ₐ[L] L) where
  toFun := extL h
  invFun := resF h
  left_inv Φ := by
    apply AlgHom.ext; intro θ
    rw [resF_apply, extL_tmul, one_mul]
  right_inv Φ' := by
    apply Algebra.TensorProduct.ext'
    intro c θ
    rw [extL_tmul, resF_apply]
    have : c ⊗ₜ[F] θ = c • ((1 : L) ⊗ₜ[F] θ) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]

noncomputable def ptChar [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    (↥(CSub h) →ₐ[F] L) ≃ (↥S →* L) :=
  (extEquiv h).trans (((Ψ h hev).arrowCongr AlgEquiv.refl).symm.trans (MonoidAlgebra.lift L L ↥S).symm)

theorem ptChar_apply [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S))
    (Φ : ↥(CSub h) →ₐ[F] L) (ν : ↥S) : ptChar h hev Φ ν = extL h Φ (dElt h ν) := by
  show extL h Φ ((Ψ h hev) (MonoidAlgebra.single ν 1)) = _
  rw [Ψ_single, one_smul]

end Points

end P2MMultE

namespace P2MMultE

open scoped TensorProduct

section ComulStable

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def ofDualQ (h : PtHyp S) : Module.Dual F (QS S) →ₗ[F] CartierDual F A :=
  (CSub h).val.toLinearMap ∘ₗ (toDualQEquiv h).symm.toLinearMap

theorem ofDualQ_mem (h : PtHyp S) (φ : Module.Dual F (QS S)) : ofDualQ h φ ∈ CSub h :=
  ((toDualQEquiv h).symm φ).2

theorem ofDualQ_apply (h : PtHyp S) (φ : Module.Dual F (QS S)) (a : A) :
    ofDualQ h φ a = φ (Ideal.Quotient.mk _ a) := by
  have : toDualQ h ((toDualQEquiv h).symm φ) = φ := (toDualQEquiv h).apply_symm_apply φ
  have h2 := LinearMap.congr_fun this (Ideal.Quotient.mk _ a)
  rw [toDualQ_mk] at h2
  exact h2

theorem range_ofDualQ (h : PtHyp S) : LinearMap.range (ofDualQ h) = (CSub h).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩; exact ofDualQ_mem h φ
  · intro θ hθ
    refine ⟨toDualQ h ⟨θ, hθ⟩, ?_⟩
    apply CartierDual.ext; intro a
    rw [ofDualQ_apply, toDualQ_mk]

noncomputable def mulDualQ (h : PtHyp S) (θ : ↥(CSub h)) : Module.Dual F (QS S ⊗[F] QS S) :=
  toDualQ h θ ∘ₗ LinearMap.mul' F (QS S)

theorem comul_mem_span_charSub (h : PtHyp S) (θ : ↥(CSub h)) :
    Coalgebra.comul (R := F) (θ.1 : CartierDual F A)
      ∈ Submodule.span F (Set.image2 (· ⊗ₜ[F] ·) ((CSub h : Set (CartierDual F A))) ((CSub h : Set (CartierDual F A)))) := by
  classical

  let ξ : Module.Dual F (QS S) ⊗[F] Module.Dual F (QS S) :=
    (TensorProduct.dualDistribEquiv F (QS S) (QS S)).symm (mulDualQ h θ)
  have hξ : TensorProduct.dualDistrib F (QS S) (QS S) ξ = mulDualQ h θ :=
    (TensorProduct.dualDistribEquiv F (QS S) (QS S)).apply_symm_apply _

  have hmem : TensorProduct.map (ofDualQ h) (ofDualQ h) ξ
      ∈ Submodule.span F (Set.image2 (· ⊗ₜ[F] ·) ((CSub h : Set (CartierDual F A))) ((CSub h : Set (CartierDual F A)))) := by
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul φ φ' =>
      rw [TensorProduct.map_tmul]
      exact Submodule.subset_span ⟨_, ofDualQ_mem h φ, _, ofDualQ_mem h φ', rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

  have heq : (Coalgebra.comul (R := F) (θ.1 : CartierDual F A)) = TensorProduct.map (ofDualQ h) (ofDualQ h) ξ := by
    apply CartierDual.tmul_eq_of_pairing_eq
    intro a b
    rw [CartierDual.comul_pairing]

    have key : ∀ z : Module.Dual F (QS S) ⊗[F] Module.Dual F (QS S),
        TensorProduct.dualDistrib F A A (TensorProduct.map (CartierDual.toDual F A).toLinearMap
          (CartierDual.toDual F A).toLinearMap (TensorProduct.map (ofDualQ h) (ofDualQ h) z)) (a ⊗ₜ[F] b)
          = TensorProduct.dualDistrib F (QS S) (QS S) z (Ideal.Quotient.mk _ a ⊗ₜ[F] Ideal.Quotient.mk _ b) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | tmul φ φ' =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
          TensorProduct.dualDistrib_apply]
        show ofDualQ h φ a * ofDualQ h φ' b = _
        rw [ofDualQ_apply, ofDualQ_apply]
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    rw [key, hξ, mulDualQ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply, ← map_mul, toDualQ_mk]
  rw [heq]
  exact hmem

end ComulStable

end P2MMultE

end P13_T5_FIELD

section P13_T5_INTEGRAL

namespace P2MMultE

open scoped TensorProduct

section TTGFComul

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F]
variable {G : Type} [CommRing G] [Bialgebra R G]

theorem tensorToGenericFibre_comul (g : G) :
    tensorToGenericFibre R F (Coalgebra.comul (R := R) g)
      = Coalgebra.comul (R := F) ((1 : F) ⊗ₜ[R] g) := by
  rw [TensorProduct.comul_tmul]
  have h1 : Coalgebra.comul (R := F) (1 : F) = (1 : F) ⊗ₜ[F] (1 : F) := by simp
  rw [h1]
  induction (Coalgebra.comul (R := R) g) using TensorProduct.induction_on with
  | zero => rw [tensorToGenericFibre_zero, TensorProduct.tmul_zero, map_zero]
  | tmul g₁ g₂ =>
    rw [tensorToGenericFibre_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add x y hx hy => rw [tensorToGenericFibre_add, TensorProduct.tmul_add, map_add, hx, hy]

end TTGFComul

section GenericFibreCoe

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F]
variable {G : Type} [CommRing G] [Algebra R G]

theorem coe_genericFibreAlgEquiv [IsDomain R] [IsFractionRing R F] (B : Subalgebra F (F ⊗[R] G))
    (x : F ⊗[R] ↥(flatClosure B)) : (genericFibreAlgEquiv B x : F ⊗[R] G) = genericFibreAlgHom B x := rfl

end GenericFibreCoe

def convEquiv (X : Type*) : WithConv X ≃ X :=
  ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩

section LiftGeneric

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]
variable {C : Type*} [CommRing C] [Algebra R C] [Algebra K C] [IsScalarTower R K C]
variable {B : Type*} [CommRing B] [Algebra R B]

noncomputable def liftS (ψ : B →ₐ[R] C) : K ⊗[R] B →ₐ[K] C :=
  Algebra.TensorProduct.lift (Algebra.ofId K C) ψ (fun _ _ => Commute.all _ _)

theorem liftS_tmul (ψ : B →ₐ[R] C) (k : K) (b : B) : liftS K ψ (k ⊗ₜ[R] b) = algebraMap K C k * ψ b := by
  simp only [liftS, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

variable {K} in

noncomputable def resS (Φ : K ⊗[R] B →ₐ[K] C) : B →ₐ[R] C :=
  (Φ.restrictScalars R).comp Algebra.TensorProduct.includeRight

variable {K} in
theorem resS_apply (Φ : K ⊗[R] B →ₐ[K] C) (b : B) : resS Φ b = Φ ((1 : K) ⊗ₜ[R] b) := rfl

noncomputable def liftSEquiv : (B →ₐ[R] C) ≃ (K ⊗[R] B →ₐ[K] C) where
  toFun := liftS K
  invFun := resS
  left_inv ψ := by
    apply AlgHom.ext; intro b
    rw [resS_apply, liftS_tmul, map_one, one_mul]
  right_inv Φ := by
    apply Algebra.TensorProduct.ext'
    intro k b
    rw [liftS_tmul, resS_apply]
    have : k ⊗ₜ[R] b = k • ((1 : K) ⊗ₜ[R] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, Algebra.smul_def]

theorem liftSEquiv_apply (ψ : B →ₐ[R] C) : liftSEquiv K ψ = liftS K ψ := rfl

end LiftGeneric

section ConvBridge

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Bialgebra R H]
variable {C : Type*} [CommRing C] [Algebra R C]

theorem brConv_mul_apply (x y : WithConv (H →ₐ[R] C)) (a : H) :
    (x * y).ofConv a = Algebra.TensorProduct.lmul' R (S := C)
      (Algebra.TensorProduct.map x.ofConv y.ofConv (Coalgebra.comul (R := R) a)) := rfl

theorem brConv_one_apply (a : H) :
    (1 : WithConv (H →ₐ[R] C)).ofConv a = algebraMap R C (Coalgebra.counit (R := R) a) := rfl

end ConvBridge

section GroupLikeOfAlgHom

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Bialgebra R B]
  [Module.Finite R B] [Module.Free R B]

theorem comul_ofDual_algHom (φ : B →ₐ[R] R) :
    Coalgebra.comul (R := R) (CartierDual.ofDual R B φ.toLinearMap)
      = CartierDual.ofDual R B φ.toLinearMap ⊗ₜ[R] CartierDual.ofDual R B φ.toLinearMap := by
  apply CartierDual.tmul_eq_of_pairing_eq
  intro a b
  rw [CartierDual.comul_pairing, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
  simp only [LinearEquiv.coe_coe, CartierDual.toDual_ofDual, AlgHom.toLinearMap_apply,
    CartierDual.ofDual_apply, map_mul]

theorem counit_ofDual_algHom (φ : B →ₐ[R] R) :
    Coalgebra.counit (R := R) (CartierDual.ofDual R B φ.toLinearMap) = 1 := by
  rw [CartierDual.counit_apply, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, map_one]

end GroupLikeOfAlgHom

section EvCS

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def evCS (h : PtHyp S) (w : L ⊗[F] ↥(CSub h)) (x : A) : L :=
  Θ h w ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk (vanishingIdeal (ptSet S)) x)

theorem evCS_tmul (h : PtHyp S) (c : L) (θ : ↥(CSub h)) (x : A) :
    evCS h (c ⊗ₜ[F] θ) x = c * algebraMap F L ((θ : CartierDual F A) x) := by
  rw [evCS, Θ_tmul_tmul, one_mul, toDualQ_mk]

theorem evCS_add (h : PtHyp S) (w w' : L ⊗[F] ↥(CSub h)) (x : A) :
    evCS h (w + w') x = evCS h w x + evCS h w' x := by
  simp only [evCS, map_add, LinearMap.add_apply]

theorem evCS_zero (h : PtHyp S) (x : A) : evCS h 0 x = 0 := by
  simp only [evCS, map_zero, LinearMap.zero_apply]

theorem evCS_dElt (h : PtHyp S) (ν : ↥S) (x : A) :
    evCS h (dElt h ν) x = (WithConv.ofConv ν.1) x := by
  rw [evCS, Θ_dElt, AlgHom.toLinearMap_apply, ptQL_tmul, one_mul, ptQ_mk]

end EvCS

section Integral

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

section BCRebuild

variable (O' : Type) [CommRing O'] (F' : Type) [Field F'] [Algebra O' F']
variable (A' : Type) [CommRing A'] [HopfAlgebra O' A'] [Module.Finite O' A'] [Module.Free O' A'] [Coalgebra.IsCocomm O' A']

noncomputable def bc : F' ⊗[O'] CartierDual O' A' ≃ₐ[F'] CartierDual F' (F' ⊗[O'] A') :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (CartierDual.dualBaseChangeLin O' F' A')
      (CartierDual.dualBaseChangeLin_bijective O' F' A').2.1 (CartierDual.dualBaseChangeLin_bijective O' F' A').2.2.1)
    (CartierDual.dualBaseChangeLin_bijective O' F' A').1

variable {O' F' A'}

theorem bc_apply (w : F' ⊗[O'] CartierDual O' A') : bc O' F' A' w = CartierDual.dualBaseChangeLin O' F' A' w := rfl

theorem bc_tmul_tmul (c : F') (φ : CartierDual O' A') (c' : F') (a : A') :
    bc O' F' A' (c ⊗ₜ[O'] φ) (c' ⊗ₜ[O'] a) = c * c' * algebraMap O' F' (φ a) := by
  rw [bc_apply, CartierDual.dualBaseChangeLin_tmul_tmul]

theorem bc_one_tmul_antipode (g : CartierDual O' A') (x : F' ⊗[O'] A') :
    bc O' F' A' ((1 : F') ⊗ₜ[O'] HopfAlgebraStruct.antipode (R := O') g) x
      = bc O' F' A' ((1 : F') ⊗ₜ[O'] g) (HopfAlgebraStruct.antipode (R := F') x) := by
  rw [bc_apply, bc_apply]
  exact (CartierDual.dualBaseChangeLin_bijective O' F' A').2.2.2.2 g x

end BCRebuild

structure IPtHyp (S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))) : Prop extends PtHyp S where
  inv_mem : ∀ ν, ν ∈ ptSet S → ∃ ν' ∈ ptSet S,
    ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)

theorem IPtHyp.of_sep_inv
    (hsep : ∀ x : QS S ⊗[F] QS S,
      (∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν, ν ∈ ptSet S → ∃ ν' ∈ ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) : IPtHyp S :=
  { PtHyp.of_isPtSubgroup hsep with inv_mem := hinv }

theorem T4facts (h : IPtHyp S) :
    ((HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S) : Set (F ⊗[O] CartierDual O A))
        = {w | ∀ x ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
            CartierDual.dualBaseChangeLin O F A w x = 0}) ∧
    IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) ∧
    IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) :=
  HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable O F A L S h.sep h.inv_mem

noncomputable abbrev BS (h : IPtHyp S) : Subalgebra F (F ⊗[O] CartierDual O A) :=
  HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)

theorem mem_BS_iff (h : IPtHyp S) (w : F ⊗[O] CartierDual O A) :
    w ∈ BS h ↔ bc O F A w ∈ CSub h.toPtHyp := by
  rw [← SetLike.mem_coe, (T4facts h).1]
  rfl

theorem image_bc_BS (h : IPtHyp S) :
    (bc O F A) '' (BS h : Set (F ⊗[O] CartierDual O A))
      = (CSub h.toPtHyp : Set (CartierDual F (F ⊗[O] A))) := by
  ext θ
  constructor
  · rintro ⟨w, hw, rfl⟩; exact (mem_BS_iff h w).mp hw
  · intro hθ
    refine ⟨(bc O F A).symm θ, ?_, (bc O F A).apply_symm_apply θ⟩
    rw [SetLike.mem_coe, mem_BS_iff, AlgEquiv.apply_symm_apply]; exact hθ

noncomputable abbrev ES (h : IPtHyp S) : Subalgebra O (CartierDual O A) :=
  HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)

theorem mem_ES_iff (h : IPtHyp S) (g : CartierDual O A) :
    g ∈ ES h ↔ bc O F A ((1 : F) ⊗ₜ[O] g) ∈ CSub h.toPtHyp := mem_BS_iff h _

theorem mem_ES_iff' (h : IPtHyp S) (g : CartierDual O A) :
    g ∈ ES h ↔ ∀ x ∈ vanishingIdeal (ptSet S), bc O F A ((1 : F) ⊗ₜ[O] g) x = 0 := mem_BS_iff h _

theorem isComulStable_BS (h : IPtHyp S) : IsComulStable O F (BS h) := (T4facts h).2.1

theorem isAntipodeStable_BS (h : IPtHyp S) : IsAntipodeStable O F (BS h) := (T4facts h).2.2

@[reducible] noncomputable def hopfES (h : IPtHyp S) : HopfAlgebra O ↥(ES h) :=
  closureHopfAlgebra O F (isComulStable_BS h) (isAntipodeStable_BS h)

theorem isCocommES (h : IPtHyp S) :
    letI := hopfES h
    Coalgebra.IsCocomm O ↥(ES h) :=
  closureIsCocomm (isComulStable_BS h)

scoped instance instModuleFiniteES (h : IPtHyp S) : Module.Finite O ↥(ES h) := flatClosure_finite (BS h)

scoped instance instModuleFreeES (h : IPtHyp S) : Module.Free O ↥(ES h) := flatClosure_free (BS h)

scoped instance instModuleFlatES (h : IPtHyp S) : Module.Flat O ↥(ES h) := flatClosure_flat (BS h)

theorem tensorInclusion_comul_ES (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    tensorInclusion (BS h) (Coalgebra.comul (R := O) e) = Coalgebra.comul (R := O) (e : CartierDual O A) := by
  letI := hopfES h
  exact tensorInclusion_closureComul (isComulStable_BS h) e

theorem counit_ES (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := O) e = (e : CartierDual O A) 1 := by
  letI := hopfES h
  show Coalgebra.counit (R := O) (e : CartierDual O A) = _
  rw [CartierDual.counit_apply]

theorem counit_ES' (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := O) e = Coalgebra.counit (R := O) (e : CartierDual O A) := rfl

theorem coe_antipode_ES (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    ((HopfAlgebraStruct.antipode (R := O) e : ↥(ES h)) : CartierDual O A)
      = HopfAlgebraStruct.antipode (R := O) (e : CartierDual O A) := rfl

noncomputable def genericFibreES (h : IPtHyp S) : F ⊗[O] ↥(ES h) ≃ₐ[F] ↥(CSub h.toPtHyp) :=
  (genericFibreAlgEquiv (BS h)).trans
    (((bc O F A).subalgebraMap (BS h)).trans
      (Subalgebra.equivOfEq _ _ (by
        apply SetLike.coe_injective
        rw [Subalgebra.coe_map]
        exact image_bc_BS h)))

theorem coe_genericFibreES (h : IPtHyp S) (y : F ⊗[O] ↥(ES h)) :
    ((genericFibreES h y : ↥(CSub h.toPtHyp)) : CartierDual F (F ⊗[O] A))
      = bc O F A (genericFibreAlgHom (BS h) y) := rfl

theorem coe_genericFibreES_tmul (h : IPtHyp S) (c : F) (e : ↥(ES h)) :
    ((genericFibreES h (c ⊗ₜ[O] e) : ↥(CSub h.toPtHyp)) : CartierDual F (F ⊗[O] A))
      = bc O F A (c ⊗ₜ[O] (e : CartierDual O A)) := by
  rw [coe_genericFibreES, genericFibreAlgHom_tmul]

theorem CSub_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : PtHyp S) (h' : PtHyp S')
    (hle : S ≤ S') : CSub h ≤ CSub h' :=
  fun _ hθ a ha => hθ a (vanishingIdeal_antitone (HopfAlgebra.ptSet_mono hle) ha)

theorem BS_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') : BS h ≤ BS h' :=
  HopfAlgebra.characterGenericFibre_mono O F A L (HopfAlgebra.ptSet_mono hle)

theorem ES_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') : ES h ≤ ES h' :=
  HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle)

end Integral

section IntegralPts

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

abbrev ptsE (h : IPtHyp S) : Type _ := WithConv (↥(ES h) →ₐ[O] L)

noncomputable def Ω (h : IPtHyp S) : L ⊗[O] ↥(ES h) ≃ₐ[L] L ⊗[F] ↥(CSub h.toPtHyp) :=
  (Algebra.TensorProduct.cancelBaseChange O F L L ↥(ES h)).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (genericFibreES h))

theorem Ω_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) :
    Ω h (c ⊗ₜ[O] e) = c ⊗ₜ[F] genericFibreES h ((1 : F) ⊗ₜ[O] e) := by
  rw [Ω, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

noncomputable def β (h : IPtHyp S) : (↥(ES h) →ₐ[O] L) ≃ (↥(CSub h.toPtHyp) →ₐ[F] L) :=
  (liftSEquiv F).trans (AlgEquiv.arrowCongr (genericFibreES h) AlgEquiv.refl)

theorem β_apply (h : IPtHyp S) (ψ : ↥(ES h) →ₐ[O] L) (θ : ↥(CSub h.toPtHyp)) :
    β h ψ θ = liftS F ψ ((genericFibreES h).symm θ) := by
  rw [β, Equiv.trans_apply, AlgEquiv.arrowCongr_apply, liftSEquiv_apply]
  rfl

noncomputable def chi [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) :
    ptsE h ≃ (↥S →* L) :=
  ((convEquiv _).trans (β h)).trans (ptChar h.toPtHyp hev)

theorem chi_apply [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ : ptsE h) (ν : ↥S) :
    chi h hev ψ ν = extL h.toPtHyp (β h ψ.ofConv) (dElt h.toPtHyp ν) := by
  rw [chi, Equiv.trans_apply, Equiv.trans_apply, ptChar_apply]
  rfl

theorem extL_β_Ω (h : IPtHyp S) (ψ : ↥(ES h) →ₐ[O] L) (z : L ⊗[O] ↥(ES h)) :
    extL h.toPtHyp (β h ψ) (Ω h z) = liftS L ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [Ω_tmul, extL_tmul, β_apply, AlgEquiv.symm_apply_apply, liftS_tmul, liftS_tmul, map_one, one_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def dhat (h : IPtHyp S) (ν : ↥S) : L ⊗[O] ↥(ES h) := (Ω h).symm (dElt h.toPtHyp ν)

theorem Ω_dhat (h : IPtHyp S) (ν : ↥S) : Ω h (dhat h ν) = dElt h.toPtHyp ν :=
  AlgEquiv.apply_symm_apply _ _

theorem chi_apply' [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ : ptsE h) (ν : ↥S) :
    chi h hev ψ ν = liftS L ψ.ofConv (dhat h ν) := by
  rw [chi_apply, ← extL_β_Ω, Ω_dhat]

noncomputable def jL (h : IPtHyp S) : L ⊗[O] ↥(ES h) →ₐ[L] CartierDual L (L ⊗[O] A) :=
  (bc O L A : L ⊗[O] CartierDual O A →ₐ[L] CartierDual L (L ⊗[O] A)).comp
    (Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val)

theorem jL_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) :
    jL h (c ⊗ₜ[O] e) = bc O L A (c ⊗ₜ[O] (e : CartierDual O A)) := rfl

theorem jL_tmul_apply_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) (c' : L) (a : A) :
    jL h (c ⊗ₜ[O] e) (c' ⊗ₜ[O] a) = c * c' * algebraMap O L ((e : CartierDual O A) a) := by
  rw [jL_tmul, bc_tmul_tmul]

theorem jL_apply_tmul (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) (c' : L) (a : A) :
    jL h z (c' ⊗ₜ[O] a) = c' * evCS h.toPtHyp (Ω h z) ((1 : F) ⊗ₜ[O] a) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, CartierDual.zero_apply_pt, map_zero, evCS_zero, mul_zero]
  | tmul c e =>
    rw [jL_tmul_apply_tmul, Ω_tmul, evCS_tmul, coe_genericFibreES_tmul, bc_tmul_tmul, one_mul,
      one_mul, ← IsScalarTower.algebraMap_apply]
    ring
  | add x y hx hy => rw [map_add, CartierDual.add_apply_pt, map_add, evCS_add, hx, hy, mul_add]

theorem jL_injective (h : IPtHyp S) : Function.Injective (jL h) := by
  haveI : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  haveI : Module.Flat O L := Module.Flat.trans O F L
  have hcoe : ⇑(Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val)
      = ⇑(LinearMap.lTensor L (ES h).val.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c e => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val) := by
    rw [hcoe]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  exact (bc O L A).injective.comp h1

noncomputable def ptO (ν : F ⊗[O] A →ₐ[F] L) : A →ₐ[O] L :=
  (ν.restrictScalars O).comp Algebra.TensorProduct.includeRight

theorem ptO_apply (ν : F ⊗[O] A →ₐ[F] L) (a : A) : ptO ν a = ν ((1 : F) ⊗ₜ[O] a) := rfl

theorem jL_dhat (h : IPtHyp S) (ν : ↥S) :
    jL h (dhat h ν) = CartierDual.ofDual L (L ⊗[O] A) (liftS L (ptO (WithConv.ofConv ν.1))).toLinearMap := by
  apply CartierDual.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c' a =>
    rw [jL_apply_tmul, Ω_dhat, evCS_dElt, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, liftS_tmul,
      ptO_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem pairing_map_jL_comul (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) (x y : L ⊗[O] A) :
    letI := hopfES h
    TensorProduct.dualDistrib L (L ⊗[O] A) (L ⊗[O] A)
      (TensorProduct.map (CartierDual.toDual L (L ⊗[O] A)).toLinearMap
        (CartierDual.toDual L (L ⊗[O] A)).toLinearMap
        (TensorProduct.map (jL h).toLinearMap (jL h).toLinearMap (Coalgebra.comul (R := L) z))) (x ⊗ₜ[L] y)
      = jL h z (x * y) := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    rw [CartierDual.zero_apply_pt]
    first
      | rfl
      | (erw [LinearMap.map_zero]; first | rfl | (erw [LinearMap.map_zero]; rfl))
  | add z z' hz hz' =>
    simp only [map_add]
    rw [CartierDual.add_apply_pt, ← hz, ← hz']
    first
      | rw [LinearMap.add_apply]
      | (erw [LinearMap.map_add]; rw [LinearMap.add_apply])
      | (erw [LinearMap.map_add]; rw [map_add, LinearMap.add_apply])
  | tmul c e =>
    let rr := Coalgebra.Repr.arbitrary O e
    have hco : Coalgebra.comul (R := L) (c ⊗ₜ[O] e)
        = ∑ i ∈ rr.index, ((1 : L) ⊗ₜ[O] rr.left i) ⊗ₜ[L] (c ⊗ₜ[O] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    have hpair : ∀ a b : A,
        ∑ i ∈ rr.index, algebraMap O L ((rr.left i : CartierDual O A) a)
            * algebraMap O L ((rr.right i : CartierDual O A) b)
          = algebraMap O L ((e : CartierDual O A) (a * b)) := by
      intro a b
      rw [← CartierDual.comul_pairing (e : CartierDual O A) a b, ← tensorInclusion_comul_ES h e, ← rr.eq,
        map_sum, map_sum, map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tensorInclusion_tmul, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, map_mul]
      rfl

    induction x using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, zero_mul, map_zero]
    | add x₁ x₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, h₁, h₂, add_mul, map_add]
    | tmul c₁ a =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, mul_zero, map_zero]
      | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, h₁, h₂, mul_add, map_add]
      | tmul c₂ a' =>
        trans ∑ i ∈ rr.index, jL h ((1 : L) ⊗ₜ[O] rr.left i) (c₁ ⊗ₜ[O] a) * jL h (c ⊗ₜ[O] rr.right i) (c₂ ⊗ₜ[O] a')
        · rw [hco, map_sum]
          simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
          erw [map_sum]
          rw [map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          erw [TensorProduct.map_tmul]
          erw [TensorProduct.dualDistrib_apply]
          rfl
        · rw [Algebra.TensorProduct.tmul_mul_tmul, jL_tmul_apply_tmul, ← hpair a a', Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [jL_tmul_apply_tmul, jL_tmul_apply_tmul]
          ring

theorem counit_jL (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := L) (jL h z) = Coalgebra.counit (R := L) z := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [jL_tmul, CartierDual.counit_apply, Algebra.TensorProduct.one_def, bc_tmul_tmul, mul_one,
      TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_comm]
    show _ = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)) * c
    rw [CartierDual.counit_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isGroupLikeElem_dhat (h : IPtHyp S) (ν : ↥S) :
    letI := hopfES h
    IsGroupLikeElem L (dhat h ν) := by
  letI := hopfES h
  have hj := jL_dhat h ν
  let J : L ⊗[O] ↥(ES h) →ₗ[L] CartierDual L (L ⊗[O] A) := (jL h).toLinearMap
  have hJ : Function.Injective J := jL_injective h
  have hJJ : Function.Injective (TensorProduct.map J J) := TensorProduct.map_injective_of_flat_flat J J hJ hJ
  constructor
  · rw [← counit_jL h, hj, counit_ofDual_algHom]
  · have key : TensorProduct.map (jL h).toLinearMap (jL h).toLinearMap (Coalgebra.comul (R := L) (dhat h ν))
        = TensorProduct.map (jL h).toLinearMap (jL h).toLinearMap (dhat h ν ⊗ₜ[L] dhat h ν) := by
      apply CartierDual.tmul_eq_of_pairing_eq
      intro x y
      rw [pairing_map_jL_comul, TensorProduct.map_tmul]
      erw [TensorProduct.map_tmul]
      erw [TensorProduct.dualDistrib_apply]
      show (jL h (dhat h ν)) (x * y) = (jL h (dhat h ν)) x * (jL h (dhat h ν)) y
      rw [hj]
      simp only [CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, map_mul]
    exact hJJ key

theorem liftS_mul_apply (h : IPtHyp S) (ψ ψ' : ptsE h) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    liftS L (ψ * ψ').ofConv z = LinearMap.mul' L L
      (TensorProduct.map (liftS L ψ.ofConv).toLinearMap (liftS L ψ'.ofConv).toLinearMap
        (Coalgebra.comul (R := L) z)) := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [liftS_tmul, brConv_mul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
    induction (Coalgebra.comul (R := O) e) using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, mul_zero]
    | tmul e₁ e₂ =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, liftS_tmul, liftS_tmul, map_one, one_mul]
      ring
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, mul_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem liftS_mul_of_isGroupLikeElem (h : IPtHyp S) (ψ ψ' : ptsE h) {z : L ⊗[O] ↥(ES h)}
    (hz : letI := hopfES h; IsGroupLikeElem L z) :
    letI := hopfES h
    liftS L (ψ * ψ').ofConv z = liftS L ψ.ofConv z * liftS L ψ'.ofConv z := by
  letI := hopfES h
  rw [liftS_mul_apply, hz.comul_eq_tmul_self, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

theorem liftS_one_apply (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    liftS L (1 : ptsE h).ofConv z = Coalgebra.counit (R := L) z := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [liftS_tmul, brConv_one_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    try rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem chi_mul [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ ψ' : ptsE h) :
    letI := hopfES h
    chi h hev (ψ * ψ') = chi h hev ψ * chi h hev ψ' := by
  letI := hopfES h
  ext ν
  rw [MonoidHom.mul_apply, chi_apply', chi_apply', chi_apply',
    liftS_mul_of_isGroupLikeElem h ψ ψ' (isGroupLikeElem_dhat h ν)]

theorem chi_one [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) :
    letI := hopfES h
    chi h hev 1 = 1 := by
  letI := hopfES h
  ext ν
  rw [chi_apply', liftS_one_apply, (isGroupLikeElem_dhat h ν).counit_eq_one, MonoidHom.one_apply]

theorem chi_eq_one_iff [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ : ptsE h) :
    letI := hopfES h
    chi h hev ψ = 1 ↔ ψ = 1 := by
  letI := hopfES h
  rw [← chi_one h hev]
  exact (chi h hev).apply_eq_iff_eq

theorem chi_pow [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ : ptsE h) (n : ℕ) :
    letI := hopfES h
    chi h hev (ψ ^ n) = chi h hev ψ ^ n := by
  letI := hopfES h
  induction n with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ n ih => rw [pow_succ, pow_succ, chi_mul, ih]

theorem pts_pow_eq_one [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (n : ℕ)
    (hS : ∀ ν : ↥S, ν ^ n = 1) (ψ : ptsE h) :
    letI := hopfES h
    ψ ^ n = 1 := by
  letI := hopfES h
  rw [← chi_eq_one_iff h hev, chi_pow]
  ext ν
  rw [MonoidHom.pow_apply, ← map_pow, hS ν, map_one, MonoidHom.one_apply]

theorem chi_apply_pow_eq_one [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S))
    (ψ : ptsE h) (ν : ↥S) (N : ℕ) (hν : ν ^ N = 1) :
    chi h hev ψ ν ^ N = 1 := by
  rw [← map_pow, hν, map_one]

end IntegralPts

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE"

namespace P2MMultE

open scoped TensorProduct

theorem toConv_ofConv {X : Type*} (x : WithConv X) : WithConv.toConv x.ofConv = x := rfl

section Restriction

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable def inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') : ↥(ES h) →ₐ[O] ↥(ES h') :=
  Subalgebra.inclusion (ES_mono h h' hle)

theorem coe_inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (e : ↥(ES h)) :
    (inclES h h' hle e : CartierDual O A) = e := Subalgebra.coe_inclusion _ _

noncomputable def resE (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') : ptsE h :=
  WithConv.toConv (ψ.ofConv.comp (inclES h h' hle))

theorem resE_ofConv (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') :
    (resE h h' hle ψ).ofConv = ψ.ofConv.comp (inclES h h' hle) := rfl

theorem resE_apply (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') (e : ↥(ES h)) :
    (resE h h' hle ψ).ofConv e = ψ.ofConv (inclES h h' hle e) := rfl

noncomputable def inclESL (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') :
    L ⊗[O] ↥(ES h) →ₐ[L] L ⊗[O] ↥(ES h') :=
  Algebra.TensorProduct.map (AlgHom.id L L) (inclES h h' hle)

theorem inclESL_tmul (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (c : L) (e : ↥(ES h)) :
    inclESL h h' hle (c ⊗ₜ[O] e) = c ⊗ₜ[O] inclES h h' hle e := rfl

theorem jL_inclESL (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (z : L ⊗[O] ↥(ES h)) :
    jL h' (inclESL h h' hle z) = jL h z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e => rw [inclESL_tmul, jL_tmul, jL_tmul, coe_inclES]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem liftS_comp_inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ↥(ES h') →ₐ[O] L)
    (z : L ⊗[O] ↥(ES h)) :
    liftS L (ψ.comp (inclES h h' hle)) z = liftS L ψ (inclESL h h' hle z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e => rw [inclESL_tmul, liftS_tmul, liftS_tmul, AlgHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem inclESL_dhat (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ν : ↥S) :
    inclESL h h' hle (dhat h ν) = dhat h' ⟨ν.1, hle ν.2⟩ := by
  apply jL_injective h'
  rw [jL_inclESL, jL_dhat, jL_dhat]

theorem chi_resE [Finite ↥S] [Finite ↥S'] (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S')
    (hev : Function.Bijective (evQ S)) (hev' : Function.Bijective (evQ S')) (ψ : ptsE h') (ν : ↥S) :
    chi h hev (resE h h' hle ψ) ν = chi h' hev' ψ ⟨ν.1, hle ν.2⟩ := by
  rw [chi_apply', chi_apply', resE_ofConv, liftS_comp_inclES, inclESL_dhat]

theorem resE_mul [Finite ↥S] [Finite ↥S'] (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S')
    (hev : Function.Bijective (evQ S)) (hev' : Function.Bijective (evQ S')) (ψ ψ' : ptsE h') :
    letI := hopfES h
    letI := hopfES h'
    resE h h' hle (ψ * ψ') = resE h h' hle ψ * resE h h' hle ψ' := by
  letI := hopfES h
  letI := hopfES h'
  apply (chi h hev).injective
  rw [chi_mul]
  ext ν
  rw [chi_resE h h' hle hev hev', MonoidHom.mul_apply, chi_resE h h' hle hev hev',
    chi_resE h h' hle hev hev', chi_mul, MonoidHom.mul_apply]

theorem resE_one [Finite ↥S] [Finite ↥S'] (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S')
    (hev : Function.Bijective (evQ S)) (hev' : Function.Bijective (evQ S')) :
    letI := hopfES h
    letI := hopfES h'
    resE h h' hle 1 = 1 := by
  letI := hopfES h
  letI := hopfES h'
  apply (chi h hev).injective
  ext ν
  rw [chi_resE h h' hle hev hev', chi_one, chi_one, MonoidHom.one_apply, MonoidHom.one_apply]

theorem resE_pow [Finite ↥S] [Finite ↥S'] (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S')
    (hev : Function.Bijective (evQ S)) (hev' : Function.Bijective (evQ S')) (ψ : ptsE h') (n : ℕ) :
    letI := hopfES h
    letI := hopfES h'
    resE h h' hle (ψ ^ n) = resE h h' hle ψ ^ n := by
  letI := hopfES h
  letI := hopfES h'
  induction n with
  | zero => rw [pow_zero, pow_zero, resE_one h h' hle hev hev']
  | succ n ih => rw [pow_succ, pow_succ, resE_mul h h' hle hev hev', ih]

theorem counit_inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (e : ↥(ES h)) :
    letI := hopfES h
    letI := hopfES h'
    Coalgebra.counit (R := O) (inclES h h' hle e) = Coalgebra.counit (R := O) e := rfl

theorem resE_congr {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation L Γ₀)
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ ψ' : ptsE h')
    (hψ : ∀ e' : ↥(ES h'), v (ψ.ofConv e' - ψ'.ofConv e') < 1) (e : ↥(ES h)) :
    v ((resE h h' hle ψ).ofConv e - (resE h h' hle ψ').ofConv e) < 1 :=
  hψ (inclES h h' hle e)

theorem resE_red {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation L Γ₀)
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h')
    (hψ : letI := hopfES h'; ∀ e' : ↥(ES h'), v (ψ.ofConv e' - algebraMap O L (Coalgebra.counit (R := O) e')) < 1)
    (e : ↥(ES h)) :
    letI := hopfES h
    v ((resE h h' hle ψ).ofConv e - algebraMap O L (Coalgebra.counit (R := O) e)) < 1 :=
  hψ (inclES h h' hle e)

end Restriction
p2m_reactivate "P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE"

section Equivariance

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable abbrev galO (σ : L ≃ₐ[F] L) : L →ₐ[O] L := (σ : L →ₐ[F] L).restrictScalars O

theorem galO_apply (σ : L ≃ₐ[F] L) (c : L) : galO (O := O) σ c = σ c := rfl

theorem gal_algebraMap (σ : L ≃ₐ[F] L) (r : O) : σ (algebraMap O L r) = algebraMap O L r := by
  rw [IsScalarTower.algebraMap_apply O F L, AlgEquiv.commutes]

noncomputable def galE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) : ptsE h :=
  WithConv.toConv ((galO σ).comp ψ.ofConv)

theorem galE_ofConv (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) :
    (galE h σ ψ).ofConv = (galO σ).comp ψ.ofConv := rfl

theorem galE_apply (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) (e : ↥(ES h)) :
    (galE h σ ψ).ofConv e = σ (ψ.ofConv e) := rfl

noncomputable def twistE (h : IPtHyp S) (σ : L ≃ₐ[F] L) : L ⊗[O] ↥(ES h) →ₐ[O] L ⊗[O] ↥(ES h) :=
  Algebra.TensorProduct.map (galO σ) (AlgHom.id O ↥(ES h))

theorem twistE_tmul (h : IPtHyp S) (σ : L ≃ₐ[F] L) (c : L) (e : ↥(ES h)) :
    twistE h σ (c ⊗ₜ[O] e) = σ c ⊗ₜ[O] e := rfl

noncomputable def twistA (σ : L ≃ₐ[F] L) : L ⊗[O] A →ₐ[O] L ⊗[O] A :=
  Algebra.TensorProduct.map (galO σ) (AlgHom.id O A)

theorem twistA_tmul (σ : L ≃ₐ[F] L) (c : L) (a : A) : twistA (O := O) σ (c ⊗ₜ[O] a) = σ c ⊗ₜ[O] a := rfl

theorem liftS_gal_twistE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ↥(ES h) →ₐ[O] L) (z : L ⊗[O] ↥(ES h)) :
    liftS L ((galO σ).comp ψ) (twistE h σ z) = σ (liftS L ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [twistE_tmul, liftS_tmul, liftS_tmul, AlgHom.comp_apply, galO_apply, map_mul, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem jL_twistE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (z : L ⊗[O] ↥(ES h)) (x : L ⊗[O] A) :
    jL h (twistE h σ z) x = σ (jL h z (twistA σ.symm x)) := by
  induction z using TensorProduct.induction_on generalizing x with
  | zero => rw [map_zero, map_zero, CartierDual.zero_apply_pt, CartierDual.zero_apply_pt, map_zero]
  | tmul c e =>
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul c' a =>
      rw [twistE_tmul, twistA_tmul, jL_tmul_apply_tmul, jL_tmul_apply_tmul, map_mul, map_mul, gal_algebraMap,
        AlgEquiv.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | add z z' hz hz' =>
    simp only [map_add, CartierDual.add_apply_pt, hz, hz']

theorem twistE_dhat (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ν ν' : ↥S)
    (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    twistE h σ (dhat h ν) = dhat h ν' := by
  apply jL_injective h
  apply CartierDual.ext
  intro x
  rw [jL_twistE, jL_dhat, jL_dhat, CartierDual.ofDual_apply, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply]
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul c' a =>
    rw [twistA_tmul, liftS_tmul, liftS_tmul, ptO_apply, ptO_apply, hσ, map_mul, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, AlgEquiv.apply_symm_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem chi_galE [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (σ : L ≃ₐ[F] L)
    (ψ : ptsE h) (ν ν' : ↥S) (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    chi h hev (galE h σ ψ) ν' = σ (chi h hev ψ ν) := by
  rw [chi_apply', chi_apply', galE_ofConv, ← twistE_dhat h σ ν ν' hσ, liftS_gal_twistE]

theorem galE_mul (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ ψ' : ptsE h) :
    letI := hopfES h
    galE h σ (ψ * ψ') = galE h σ ψ * galE h σ ψ' := by
  letI := hopfES h
  rw [← toConv_ofConv (galE h σ (ψ * ψ')), ← toConv_ofConv (galE h σ ψ * galE h σ ψ')]
  congr 1
  apply AlgHom.ext
  intro e
  rw [galE_apply, brConv_mul_apply, brConv_mul_apply]
  induction (Coalgebra.comul (R := O) e) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e₁ e₂ =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, galE_apply, galE_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galE_one (h : IPtHyp S) (σ : L ≃ₐ[F] L) :
    letI := hopfES h
    galE h σ 1 = 1 := by
  letI := hopfES h
  rw [← toConv_ofConv (galE h σ 1), ← toConv_ofConv (1 : ptsE h)]
  congr 1
  apply AlgHom.ext
  intro e
  rw [galE_apply, brConv_one_apply, gal_algebraMap]

theorem galE_eq_self_iff (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) :
    galE h σ ψ = ψ ↔ ∀ e, σ (ψ.ofConv e) = ψ.ofConv e := by
  constructor
  · intro hfix e
    rw [← galE_apply h σ ψ e, hfix]
  · intro hfix
    rw [← toConv_ofConv (galE h σ ψ), ← toConv_ofConv ψ]
    congr 1
    exact AlgHom.ext hfix

end Equivariance
p2m_reactivate "P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE"

namespace P2MMultE

open scoped TensorProduct

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE"

end P13_T5_INTEGRAL
p2m_reactivate "P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.P2MMultE"

theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L] :
    ∃ χ : ∀ (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
        (_ : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
        (_ : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
        (_ : Function.Bijective (HopfAlgebra.evalQuot S)),
        WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) →ₐ[O] L) ≃ (↥S →* L),
      (∀ (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
          (hsep : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
          (hinv : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev : Function.Bijective (HopfAlgebra.evalQuot S))
          (hB : IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)))
          (hB' : IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S))),
          letI := closureHopfAlgebra O F hB hB'
          ∀ ψ ψ' : WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) →ₐ[O] L),
            χ S hsep hinv hev (ψ * ψ') = χ S hsep hinv hev ψ * χ S hsep hinv hev ψ') ∧
      (∀ (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
          (hsep : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
          (hinv : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev : Function.Bijective (HopfAlgebra.evalQuot S))
          (σ : L ≃ₐ[F] L) (ψ : WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) →ₐ[O] L)) (ν ν' : ↥S),
          (∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) →
          χ S hsep hinv hev (WithConv.toConv (((σ : L →ₐ[F] L).restrictScalars O).comp (WithConv.ofConv ψ))) ν'
            = σ (χ S hsep hinv hev ψ ν)) ∧
      (∀ (S S' : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S] [Finite ↥S']
          (hsep : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
          (hinv : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev : Function.Bijective (HopfAlgebra.evalQuot S))
          (hsep' : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S') (HopfAlgebra.pointQuot S'),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S') (hν' : ν' ∈ HopfAlgebra.ptSet S'),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S') ν ν' hν hν' x = 0) → x = 0))
          (hinv' : (∀ ν ∈ HopfAlgebra.ptSet S', ∃ ν' ∈ HopfAlgebra.ptSet S',
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev' : Function.Bijective (HopfAlgebra.evalQuot S'))
          (hle : S ≤ S') (ψ : WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')) →ₐ[O] L)) (ν : ↥S),
          χ S hsep hinv hev (WithConv.toConv ((WithConv.ofConv ψ).comp
              (Subalgebra.inclusion (HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle))))) ν
            = χ S' hsep' hinv' hev' ψ ⟨ν.1, hle ν.2⟩) := by
  refine ⟨fun S _ hsep hinv hev => P2MMultE.chi (P2MMultE.IPtHyp.of_sep_inv hsep hinv) hev, ?_, ?_, ?_⟩
  · intro S _ hsep hinv hev hB hB' ψ ψ'
    exact P2MMultE.chi_mul (P2MMultE.IPtHyp.of_sep_inv hsep hinv) hev ψ ψ'
  · intro S _ hsep hinv hev σ ψ ν ν' hσ
    exact P2MMultE.chi_galE (P2MMultE.IPtHyp.of_sep_inv hsep hinv) hev σ ψ ν ν' hσ
  · intro S S' _ _ hsep hinv hev hsep' hinv' hev' hle ψ ν
    exact P2MMultE.chi_resE (P2MMultE.IPtHyp.of_sep_inv hsep hinv) (P2MMultE.IPtHyp.of_sep_inv hsep' hinv')
      hle hev hev' ψ ν

end S_HopfAlgebra_exists_characterClosure_points_equiv
end P2MW
export P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv (solution)

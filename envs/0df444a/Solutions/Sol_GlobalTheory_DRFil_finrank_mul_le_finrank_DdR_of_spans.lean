-- Prove2me | solution 1 for GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:41:05.106151+00:00
-- url     : https://prove2.me/submissions/94f769fb-b034-4c39-9dcf-12ed839f35c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankMulLeFinrankDdROfSpans
import Theorems.Thm_GlobalTheory_DRFil_finrank_le_of_span_subspace
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
namespace GlobalTheory.DRFil
theorem _root_.solution {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F]
    [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (hs : Spans PD ρ) :
    Module.finrank Qp K * Module.finrank LL V ≤ Module.finrank LL ↥(DdR PD ρ) := by
  classical
  haveI : Nontrivial F := by
    refine nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_
    rw [h0]
    exact (PD.Fil 2).zero_mem
  unfold Spans mulR at hs
  set W := DdR PD ρ with hW
  let e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V := TensorProduct.comm Qp V F

  have he : ∀ (b : F) (x : V ⊗[Qp] F),
      e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]

  have hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W →
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W := by
    intro c x hx
    simp only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    have hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c))
          (actVdR PD ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v z => simp [actVdR]
      | add y y' hy hy' => simp only [map_add, hy, hy']
    rw [hcomm, hx g]

  let D' : Submodule K (F ⊗[Qp] V) :=
    { carrier := e '' (W : Set (V ⊗[Qp] F))
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, W.add_mem hx hy, map_add e x y⟩
      zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨_, hK c x hx, ?_⟩
        rw [he, algebraMap_smul] }
  have hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, b, d, hd, hy⟩ := hs (e.symm y)
    have hy' : y = ∑ i, b i • e (d i) := by
      rw [← e.apply_symm_apply y, hy, map_sum]
      simp only [he]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))
  haveI : FiniteDimensional LL W := hfin
  haveI : FiniteDimensional Qp W := Module.Finite.trans LL W
  let φ : W ≃ₗ[Qp] D' :=
    LinearEquiv.ofBijective
      ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩
         map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y)
         map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D')
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)),
        by rintro ⟨_, w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩⟩
  haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ
  haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'
  have h1 := finrank_le_of_span_subspace D' hspan
  rw [Module.finrank_baseChange] at h1
  have h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W := by
    rw [Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]
  have h3 : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank _ _ _
  have hpos : 0 < finrank Qp LL := Module.finrank_pos
  have key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W :=
    calc finrank Qp LL * (finrank Qp K * finrank LL V)
        = finrank Qp K * finrank Qp V := by rw [← h3]; ring
      _ ≤ finrank Qp K * finrank K D' := Nat.mul_le_mul_left _ h1
      _ = finrank Qp LL * finrank LL W := h2
  exact Nat.le_of_mul_le_mul_left key hpos
end GlobalTheory.DRFil

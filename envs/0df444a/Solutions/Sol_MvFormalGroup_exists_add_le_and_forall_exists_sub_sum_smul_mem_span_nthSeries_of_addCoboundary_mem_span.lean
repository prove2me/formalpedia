-- Prove2me | solution 1 for MvFormalGroup.exists_add_le_and_forall_exists_sub_sum_smul_mem_span_nthSeries_of_addCoboundary_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/14ccc0c5-bbe3-5fb7-bd73-67d201a3dad5

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete
import Theorems.Thm_MvFormalGroup_finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_add_le_and_forall_exists_sub_sum_smul_mem_span_nthSeries_of_addCoboundary_mem_span
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries
open scoped TensorProduct

namespace P2mFGPrimCount

section General

variable {k : Type u} [Field k] {n : ℕ}

local notation "A" => MvPowerSeries (Fin n) k

theorem exists_pow_X_mem (I : Ideal A) [Module.Finite k (A ⧸ I)] (l : Fin n) :
    ∃ N : ℕ, (X l : A) ^ N ∈ I := by
  haveI : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite k (A ⧸ I)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A ⧸ I)
  refine ⟨N, ?_⟩
  have hmem : Ideal.Quotient.mk I (X l) ∈ Ideal.jacobson (⊥ : Ideal (A ⧸ I)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add]
    refine IsUnit.map _ ?_
    rw [isUnit_iff_constantCoeff]
    simp
  have hpow : (Ideal.Quotient.mk I (X l)) ^ N ∈ (Ideal.jacobson (⊥ : Ideal (A ⧸ I))) ^ N :=
    Ideal.pow_mem_pow hmem N
  rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hpow
  exact hpow

theorem span_natCast_eq_bot (k : Type u) [Field k] (p : ℕ) [CharP k p] (T : Type*) [CommRing T]
    [Algebra k T] : Ideal.span {(p : T)} = ⊥ := by
  have hp : (p : T) = 0 := by
    rw [← map_natCast (algebraMap k T) p, CharP.cast_eq_zero, map_zero]
  rw [hp, Ideal.span_singleton_eq_bot]

theorem map_mem_radical_bot {B C : Type*} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (f : B →ₐ[k] C) {b : B} (hb : b ∈ (⊥ : Ideal B).radical) : f b ∈ (⊥ : Ideal C).radical := by
  obtain ⟨m, hm⟩ := hb
  refine ⟨m, ?_⟩
  rw [Ideal.mem_bot] at hm
  rw [← map_pow, hm, map_zero, Ideal.mem_bot]

theorem map_bot_mem_radical {B C : Type*} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (f : B →ₐ[k] C) : ∀ s ∈ (⊥ : Ideal B), f s ∈ (⊥ : Ideal C).radical := by
  intro s hs
  rw [Ideal.mem_bot] at hs
  rw [hs, map_zero]
  exact Ideal.le_radical (Ideal.zero_mem _)

end General

section TwoBlock

variable {k : Type u} [Field k] (p : ℕ) {n : ℕ} (F : MvFormalGroup n k)
  {L : Type u} [CommRing L] [HopfAlgebra k L]
  (π : MvPowerSeries (Fin n) k →ₐ[k] L)

local notation "A" => MvPowerSeries (Fin n) k
local notation "A₂" => MvPowerSeries (Fin n ⊕ Fin n) k

def Xl : Fin n → A₂ := fun l => X (Sum.inl l)

def Xr : Fin n → A₂ := fun l => X (Sum.inr l)

theorem hasSubst_Xl : HasSubst (Xl (k := k) (n := n)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_Xr : HasSubst (Xr (k := k) (n := n)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

def y : Fin n ⊕ Fin n → L ⊗[k] L :=
  Sum.elim (fun j => π (X j) ⊗ₜ[k] (1 : L)) (fun j => (1 : L) ⊗ₜ[k] π (X j))

variable {π}
variable (hrad : ∀ i, π (X i) ∈ (⊥ : Ideal L).radical)

include hrad in
theorem y_mem_radical (s : Fin n ⊕ Fin n) : y π s ∈ (⊥ : Ideal (L ⊗[k] L)).radical := by
  rcases s with j | j
  · change (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L) (π (X j)) ∈ _
    exact map_mem_radical_bot _ (hrad j)
  · change (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L) (π (X j)) ∈ _
    exact map_mem_radical_bot _ (hrad j)

def Θ : A₂ →ₐ[k] L ⊗[k] L :=
  MvFormalGroup.adicEvalAlgHom (⊥ : Ideal (L ⊗[k] L)) (y_mem_radical hrad)

theorem Θ_apply (G : A₂) : Θ hrad G = MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[k] L)) (y π) G := by
  show MvFormalGroup.adicEvalAlgHom (⊥ : Ideal (L ⊗[k] L)) (y_mem_radical hrad) G = _
  rw [MvFormalGroup.coe_adicEvalAlgHom]

theorem Θ_X (s : Fin n ⊕ Fin n) : Θ hrad (X s) = y π s := by
  rw [Θ_apply, MvFormalGroup.adicEval_X]

variable (hπev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (X i)) G)

include hπev in
theorem Θ_subst_Xl (G : A) : Θ hrad (subst Xl G) = π G ⊗ₜ[k] 1 := by
  rw [Θ_apply, MvFormalGroup.adicEval_subst (⊥ : Ideal (L ⊗[k] L)) (y_mem_radical hrad) hasSubst_Xl]
  have hfam : (fun l => MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[k] L)) (y π) (Xl l : A₂)) =
      fun l => (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L) (π (X l)) := by
    funext l
    rw [Xl, MvFormalGroup.adicEval_X]
    rfl
  rw [hfam, ← MvFormalGroup.map_adicEval (⊥ : Ideal L) (⊥ : Ideal (L ⊗[k] L))
    (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L) Submodule.fg_bot
    (map_bot_mem_radical _) hrad G, ← hπev G]
  rfl

include hπev in
theorem Θ_subst_Xr (G : A) : Θ hrad (subst Xr G) = 1 ⊗ₜ[k] π G := by
  rw [Θ_apply, MvFormalGroup.adicEval_subst (⊥ : Ideal (L ⊗[k] L)) (y_mem_radical hrad) hasSubst_Xr]
  have hfam : (fun l => MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[k] L)) (y π) (Xr l : A₂)) =
      fun l => (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L) (π (X l)) := by
    funext l
    rw [Xr, MvFormalGroup.adicEval_X]
    rfl
  rw [hfam, ← MvFormalGroup.map_adicEval (⊥ : Ideal L) (⊥ : Ideal (L ⊗[k] L))
    (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L) Submodule.fg_bot
    (map_bot_mem_radical _) hrad G, ← hπev G]
  rfl

variable (hcomulX : ∀ i, Coalgebra.comul (R := k) (π (X i)) =
    MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[k] L))
      (Sum.elim (fun j => π (X j) ⊗ₜ[k] (1 : L)) (fun j => (1 : L) ⊗ₜ[k] π (X j)))
      (F.toPowerSeries i))

include hcomulX in

theorem comul_π (G : A) : Coalgebra.comul (R := k) (π G) = Θ hrad (subst F.toPowerSeries G) := by
  set χ : A →ₐ[k] L ⊗[k] L := (Bialgebra.comulAlgHom k L).comp π with hχ
  have hχX : ∀ i, χ (X i) = MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[k] L)) (y π)
      (F.toPowerSeries i) := fun i => by
    rw [hχ, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, hcomulX i]
    rfl
  have hχrad : ∀ i, χ (X i) ∈ (⊥ : Ideal (L ⊗[k] L)).radical := fun i => by
    rw [hχX]
    exact MvFormalGroup.adicEval_mem_radical (⊥ : Ideal (L ⊗[k] L)) (y_mem_radical hrad) (F.constantCoeff_eq_zero i)
  have h1 : Coalgebra.comul (R := k) (π G) = χ G := rfl
  rw [h1, MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (L ⊗[k] L)) χ hχrad G]
  have hfam : (fun i => χ (X i)) = fun i => MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[k] L)) (y π)
      (F.toPowerSeries i) := funext hχX
  rw [hfam, ← MvFormalGroup.adicEval_subst (⊥ : Ideal (L ⊗[k] L)) (y_mem_radical hrad) F.hasSubst_toPowerSeries, Θ_apply]

def J₂ : Ideal A₂ :=
  Ideal.span (Set.range (Sum.elim (fun i => subst Xl (F.nthSeries p i)) (fun i => subst Xr (F.nthSeries p i))))

variable (hker : RingHom.ker π = Ideal.span (Set.range (F.nthSeries p)))

include hker in
theorem π_nthSeries (i : Fin n) : π (F.nthSeries p i) = 0 := by
  rw [← RingHom.mem_ker, hker]
  exact Ideal.subset_span ⟨i, rfl⟩

include hπev hker in
theorem J₂_le_ker : J₂ p F ≤ RingHom.ker (Θ hrad) := by
  rw [J₂, Ideal.span_le]
  rintro _ ⟨s, rfl⟩
  rcases s with i | i
  · change Θ hrad (subst Xl (F.nthSeries p i)) = 0
    rw [Θ_subst_Xl hrad hπev, π_nthSeries p F hker, TensorProduct.zero_tmul]
  · change Θ hrad (subst Xr (F.nthSeries p i)) = 0
    rw [Θ_subst_Xr hrad hπev, π_nthSeries p F hker, TensorProduct.tmul_zero]

include hker in
theorem map_substXl_ker_le : Ideal.map (substAlgHom (hasSubst_Xl (k := k) (n := n))) (RingHom.ker π) ≤ J₂ p F := by
  rw [hker, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact Ideal.subset_span ⟨Sum.inl i, by simp⟩

include hker in
theorem map_substXr_ker_le : Ideal.map (substAlgHom (hasSubst_Xr (k := k) (n := n))) (RingHom.ker π) ≤ J₂ p F := by
  rw [hker, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact Ideal.subset_span ⟨Sum.inr i, by simp⟩

local notation "M" => (MvPowerSeries (Fin n ⊕ Fin n) k ⧸ J₂ p F)

variable (hπ : Function.Surjective π)

def blockL : L →ₐ[k] M :=
  AlgHom.liftOfSurjective π hπ ((Ideal.Quotient.mkₐ k (J₂ p F)).comp (substAlgHom hasSubst_Xl)) (by
    intro f hf
    change Ideal.Quotient.mk (J₂ p F) (substAlgHom hasSubst_Xl f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_substXl_ker_le p F hker (Ideal.mem_map_of_mem _ hf))

def blockR : L →ₐ[k] M :=
  AlgHom.liftOfSurjective π hπ ((Ideal.Quotient.mkₐ k (J₂ p F)).comp (substAlgHom hasSubst_Xr)) (by
    intro f hf
    change Ideal.Quotient.mk (J₂ p F) (substAlgHom hasSubst_Xr f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_substXr_ker_le p F hker (Ideal.mem_map_of_mem _ hf))

theorem blockL_π (G : A) : blockL p F hker hπ (π G) = Ideal.Quotient.mk (J₂ p F) (subst Xl G) := by
  rw [blockL, AlgHom.liftOfSurjective_apply, AlgHom.comp_apply, substAlgHom_apply]
  rfl

theorem blockR_π (G : A) : blockR p F hker hπ (π G) = Ideal.Quotient.mk (J₂ p F) (subst Xr G) := by
  rw [blockR, AlgHom.liftOfSurjective_apply, AlgHom.comp_apply, substAlgHom_apply]
  rfl

def Ψ : L ⊗[k] L →ₐ[k] M :=
  Algebra.TensorProduct.lift (blockL p F hker hπ) (blockR p F hker hπ) fun _ _ => Commute.all _ _

include hker in

theorem mk_X_mem_radical [Module.Finite k (A ⧸ Ideal.span (Set.range (F.nthSeries p)))]
    (s : Fin n ⊕ Fin n) : Ideal.Quotient.mk (J₂ p F) (X s) ∈ (⊥ : Ideal M).radical := by
  rcases s with l | l
  · obtain ⟨N, hN⟩ := exists_pow_X_mem (Ideal.span (Set.range (F.nthSeries p))) l
    refine ⟨N, ?_⟩
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    have : (X (Sum.inl l) : A₂) ^ N = substAlgHom hasSubst_Xl ((X l : A) ^ N) := by
      rw [map_pow, coe_substAlgHom, subst_X hasSubst_Xl]
      rfl
    rw [this]
    refine map_substXl_ker_le p F hker (Ideal.mem_map_of_mem _ ?_)
    rw [hker]
    exact hN
  · obtain ⟨N, hN⟩ := exists_pow_X_mem (Ideal.span (Set.range (F.nthSeries p))) l
    refine ⟨N, ?_⟩
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    have : (X (Sum.inr l) : A₂) ^ N = substAlgHom hasSubst_Xr ((X l : A) ^ N) := by
      rw [map_pow, coe_substAlgHom, subst_X hasSubst_Xr]
      rfl
    rw [this]
    refine map_substXr_ker_le p F hker (Ideal.mem_map_of_mem _ ?_)
    rw [hker]
    exact hN

include hker hπ in

theorem ker_le_J₂ [Module.Finite k (A ⧸ Ideal.span (Set.range (F.nthSeries p)))] :
    RingHom.ker (Θ hrad) ≤ J₂ p F := by
  intro H hH
  rw [RingHom.mem_ker] at hH

  have hvals : ∀ s, ((Ψ p F hker hπ).comp (Θ hrad)) (X s) = Ideal.Quotient.mkₐ k (J₂ p F) (X s) := by
    intro s
    rw [AlgHom.comp_apply, Θ_X]
    rcases s with l | l
    · change Ψ p F hker hπ (π (X l) ⊗ₜ[k] 1) = _
      rw [Ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one, blockL_π, subst_X hasSubst_Xl]
      rfl
    · change Ψ p F hker hπ (1 ⊗ₜ[k] π (X l)) = _
      rw [Ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, blockR_π, subst_X hasSubst_Xr]
      rfl
  have hrad1 : ∀ s, ((Ψ p F hker hπ).comp (Θ hrad)) (X s) ∈ (⊥ : Ideal M).radical := fun s => by
    rw [hvals]; exact mk_X_mem_radical p F hker s
  have hrad2 : ∀ s, (Ideal.Quotient.mkₐ k (J₂ p F)) (X s) ∈ (⊥ : Ideal M).radical := fun s =>
    mk_X_mem_radical p F hker s
  have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal M) _ hrad1 H
  have h2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal M) _ hrad2 H
  have hfam : (fun s => ((Ψ p F hker hπ).comp (Θ hrad)) (X s)) =
      fun s => (Ideal.Quotient.mkₐ k (J₂ p F)) (X s) := funext hvals
  rw [hfam, ← h2, AlgHom.comp_apply, hH, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

end TwoBlock

section Primitive

variable {k : Type u} [Field k] {L : Type u} [CommRing L] [HopfAlgebra k L]

theorem mem_primitives_iff (x : L) :
    x ∈ primitives k L ↔ Coalgebra.comul (R := k) x - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x = 0 := by
  rw [primitives, LinearMap.mem_ker]
  rfl

theorem counit_eq_zero_of_mem_primitives {x : L} (hx : x ∈ primitives k L) :
    Coalgebra.counit (R := k) x = 0 := by
  rw [mem_primitives_iff, sub_sub, sub_eq_zero] at hx
  have h1 := Coalgebra.rTensor_counit_comul (R := k) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Bialgebra.counit_one] at h1

  have h2 := congrArg (fun t => Coalgebra.counit (R := k) (TensorProduct.lid k L t)) h1
  simp only [map_add, TensorProduct.lid_tmul, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one,
    one_smul] at h2
  linear_combination h2

end Primitive

end P2mFGPrimCount

end

open scoped TensorProduct in
open MvPowerSeries P2mFGPrimCount in
theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h) :
    ∃ (s : ℕ) (ψ : Fin s → MvPowerSeries (Fin n) k), s + n ≤ h ∧
      (∀ j, MvPowerSeries.constantCoeff (ψ j) = 0 ∧
        F₀.addCoboundary (ψ j) ∈ Ideal.span (Set.range (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
            (F₀.nthSeries p i))
          (fun i => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
            (F₀.nthSeries p i))))) ∧
      ∀ ψ' : MvPowerSeries (Fin n) k, MvPowerSeries.constantCoeff ψ' = 0 →
        F₀.addCoboundary ψ' ∈ Ideal.span (Set.range (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
            (F₀.nthSeries p i))
          (fun i => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
            (F₀.nthSeries p i)))) →
        ∃ a : Fin s → k, ψ' - ∑ j, a j • ψ j ∈ Ideal.span (Set.range (F₀.nthSeries p)) := by
  classical
  set I : Ideal (MvPowerSeries (Fin n) k) := Ideal.span (Set.range (F₀.nthSeries p)) with hI

  have hp : Fact p.Prime := inferInstance
  haveI hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ I) :=
    Module.finite_of_finrank_pos (by rw [hh]; exact pow_pos hp.out.pos h)
  haveI : IsAdicComplete (Ideal.span {(p : k)}) k := by
    rw [span_natCast_eq_bot k p k]; infer_instance
  have hnil : ∀ i : Fin n, ∃ N : ℕ, (X i : MvPowerSeries (Fin n) k) ^ N ∈
      Ideal.span (Set.range (F₀.nthSeries p)) ⊔ Ideal.span {(p : MvPowerSeries (Fin n) k)} := by
    intro i
    obtain ⟨N, hN⟩ := exists_pow_X_mem I i
    exact ⟨N, Ideal.mem_sup_left hN⟩
  obtain ⟨L, _, _, _, _, _, π, hπ, hker, hrad, hπev, hcomulX, hcounit⟩ :=
    MvFormalGroup.exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete
      (𝓞 := k) p F₀ p hnil
  rw [span_natCast_eq_bot k p L] at hrad hπev
  rw [span_natCast_eq_bot k p (L ⊗[k] L)] at hcomulX

  have hΘl : ∀ G : MvPowerSeries (Fin n) k, Θ hrad (subst
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = π G ⊗ₜ[k] 1 :=
    fun G => Θ_subst_Xl hrad hπev G
  have hΘr : ∀ G : MvPowerSeries (Fin n) k, Θ hrad (subst
      (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = 1 ⊗ₜ[k] π G :=
    fun G => Θ_subst_Xr hrad hπev G
  have hcomul : ∀ G, Coalgebra.comul (R := k) (π G) = Θ hrad (subst F₀.toPowerSeries G) :=
    fun G => comul_π (F := F₀) hrad hcomulX G
  have hkerΘ : RingHom.ker (Θ hrad) = J₂ p F₀ :=
    le_antisymm (ker_le_J₂ p F₀ hrad hker hπ) (J₂_le_ker p F₀ hrad hπev hker)

  have hΘcob : ∀ ψ : MvPowerSeries (Fin n) k,
      Θ hrad (F₀.addCoboundary ψ) = Coalgebra.comul (R := k) (π ψ) - π ψ ⊗ₜ[k] 1 - 1 ⊗ₜ[k] π ψ := by
    intro ψ
    rw [MvFormalGroup.addCoboundary, map_sub, map_sub, hcomul, hΘl, hΘr]
  have hprim_iff : ∀ ψ : MvPowerSeries (Fin n) k, π ψ ∈ primitives k L ↔ F₀.addCoboundary ψ ∈ J₂ p F₀ := by
    intro ψ
    rw [mem_primitives_iff, ← hΘcob, ← hkerΘ, RingHom.mem_ker]

  have hcount : Module.finrank k ↥(primitives k L) + n ≤ h :=
    MvFormalGroup.finrank_primitives_add_le_of_ker_eq_span_nthSeries_of_finrank_eq_pow p F₀ h hh π hπ hker
      (Θ hrad) hΘl hΘr hcomul hcounit
  set P : Submodule k L := primitives k L with hP
  set s : ℕ := Module.finrank k ↥P with hs
  let b : Module.Basis (Fin s) k ↥P := Module.finBasis k ↥P
  let ψ : Fin s → MvPowerSeries (Fin n) k := fun j => (hπ (b j : L)).choose
  have hψ : ∀ j, π (ψ j) = (b j : L) := fun j => (hπ (b j : L)).choose_spec
  refine ⟨s, ψ, hcount, fun j => ⟨?_, ?_⟩, fun ψ' _ hJ => ?_⟩
  · rw [← hcounit, hψ]
    exact counit_eq_zero_of_mem_primitives (b j).2
  · have := (hprim_iff (ψ j)).mp (by rw [hψ]; exact (b j).2)
    exact this
  · have hmem : π ψ' ∈ P := (hprim_iff ψ').mpr hJ
    let a : Fin s → k := fun j => b.repr ⟨π ψ', hmem⟩ j
    refine ⟨a, ?_⟩
    rw [hI, ← hker, RingHom.mem_ker, map_sub, map_sum, sub_eq_zero]
    have hsum := b.sum_repr ⟨π ψ', hmem⟩
    have hsum' := congrArg (fun t : ↥P => (t : L)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum'
    rw [← hsum']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hψ]

end S_MvFormalGroup_exists_add_le_and_forall_exists_sub_sum_smul_mem_span_nthSeries_of_addCoboundary_mem_span
end P2MW
export P2MW.S_MvFormalGroup_exists_add_le_and_forall_exists_sub_sum_smul_mem_span_nthSeries_of_addCoboundary_mem_span (solution)

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Lattice.exists_basis_of_pid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:26.11081+00:00
-- url     : https://prove2.me/submissions/e3f875d5-9a79-4659-b4a4-9c80f04fd6db

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Lattice_exists_common_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Lattice
open CompanionTheory.Rg.FlB
open scoped NormedField Valued
namespace GlobalTheory.CompanionTheory.Lattice
theorem _root_.solution {L V : Type} [Field L] [AddCommGroup V] [Module L V] (O : Subring L)
    [IsPrincipalIdealRing O]
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) {m : ℕ}
    (b : Module.Basis (Fin m) L V) (Λ : AddSubgroup V) (c : L) (hc : c ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ i, b.repr (c • x) i ∈ O) (hspan : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ Λ)
    (hO : ∀ a ∈ O, ∀ x ∈ Λ, a • x ∈ Λ) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) L V), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ O := by
  classical

  let ψ : (Fin m → O) →ₗ[O] V :=
    { toFun := fun y => c⁻¹ • ∑ j, (y j : L) • b j
      map_add' := fun y z => by
        simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a y => by
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          Subring.coe_mul, mul_smul]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  have hψ : ∀ y, ψ y = c⁻¹ • ∑ j, (y j : L) • b j := fun _ => rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    rw [hψ] at hy
    have h0 : ∑ j, (y j : L) • b j = 0 := (smul_eq_zero.1 hy).resolve_left (inv_ne_zero hc)
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => (y j : L)) h0
    exact funext fun j => Subtype.ext (this j)
  let N : Submodule O (Fin m → O) :=
    { carrier := {y | ψ y ∈ Λ}
      add_mem' := fun {y z} hy hz => by
        simpa [map_add] using Λ.add_mem hy hz
      zero_mem' := by simp [Λ.zero_mem]
      smul_mem' := fun a y hy => by
        simpa [map_smul, Subring.smul_def] using hO a a.2 _ hy }
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin m)) N
  let v : Fin n → V := fun i => ψ (bN i : Fin m → O)
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (bN i).2

  have hrep : ∀ z ∈ Λ, ∃ o : Fin n → O, z = ∑ i, (o i : L) • v i := by
    intro z hz
    let y : Fin m → O := fun j => ⟨b.repr (c • z) j, h1 z hz j⟩
    have hy : ψ y = z := by
      rw [hψ]
      have : ∑ j, (y j : L) • b j = c • z := b.sum_repr (c • z)
      rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hyN : y ∈ N := by
      change ψ y ∈ Λ
      rwa [hy]
    refine ⟨fun i => bN.repr ⟨y, hyN⟩ i, ?_⟩
    have h2 := congrArg (fun w : N => ψ (w : Fin m → O)) (bN.sum_repr ⟨y, hyN⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hy] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Subring.smul_def]

  have hliO : LinearIndependent O v := by
    have h3 : LinearIndependent O (fun i => (bN i : Fin m → O)) :=
      bN.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    exact h3.map' ψ hinj
  have hli : LinearIndependent L v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain ⟨d, hd, hdg⟩ := exists_common_denom O hfrac Finset.univ g
    have h4 : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = 0 := by
      have : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j
          = (d : L) • ∑ j, g j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Subring.smul_def, mul_smul]
      rw [this, hg, smul_zero]
    have h5 := Fintype.linearIndependent_iff.1 hliO _ h4 i
    have h6 : (d : L) * g i = 0 := congrArg Subtype.val h5
    exact (mul_eq_zero.1 h6).resolve_left hd
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, ha, hax⟩ := hspan x
    obtain ⟨o, ho⟩ := hrep _ hax
    have hx : x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx, ho]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => by simp [B]
  refine ⟨n, B, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · obtain ⟨o, ho⟩ := hrep x hx
    have h7 : x = ∑ j, (o j : L) • B j := by simpa only [hB] using ho
    have h8 : B.repr x i = (o i : L) := by
      rw [h7, B.repr_sum_self]
    rw [h8]
    exact (o i).2
  · rw [← B.sum_repr x]
    exact Λ.sum_mem fun i _ => hO _ (hx i) _ (by rw [hB]; exact hvΛ i)
end GlobalTheory.CompanionTheory.Lattice

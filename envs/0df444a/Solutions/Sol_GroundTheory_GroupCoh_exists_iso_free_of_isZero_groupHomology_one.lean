-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_iso_free_of_isZero_groupHomology_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:08.002005+00:00
-- url     : https://prove2.me/submissions/90ccd7b0-c414-4786-93c2-e8ba6df9fe07

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
import Theorems.Thm_GroundTheory_GroupCoh_injective_of_isZero_groupHomology_one
import Theorems.Thm_GroundTheory_GroupCoh_eq_top_of_sup_coinvariantsKer_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) (M : Rep.{u} k G)
    (hM : IsZero (groupHomology M 1)) : ∃ ι : Type u, Nonempty (Rep.free k G ι ≅ M) := by
  classical

  let ι := Module.Free.ChooseBasisIndex k (Coinvariants M.ρ)
  let b : Module.Basis ι k (Coinvariants M.ρ) := Module.Free.chooseBasis k (Coinvariants M.ρ)
  choose e he using fun i => Coinvariants.mk_surjective M.ρ (b i)
  let π : Rep.free k G ι ⟶ M := Rep.freeLift (k := k) (G := G) (A := M) e
  have hπ : ∀ i g r, π.hom (single i (MonoidAlgebra.single g r)) = r • M.ρ g (e i) :=
    fun i g r => by simp [π]

  have hsurj : Function.Surjective π.hom := by
    have hr : LinearMap.range π.hom.toLinearMap = ⊤ := by
      apply eq_top_of_sup_coinvariantsKer_eq_top hG M.ρ
      · rintro g _ ⟨y, rfl⟩
        exact LinearMap.mem_range.mpr ⟨(Rep.free k G ι).ρ g y, Rep.hom_comm_apply π g y⟩
      · rw [eq_top_iff]
        intro x _
        have hx : Coinvariants.mk M.ρ x ∈ Submodule.span k (Set.range b) :=
          b.span_eq ▸ Submodule.mem_top
        have hmap : Submodule.span k (Set.range b) ≤
            (LinearMap.range π.hom.toLinearMap).map (Coinvariants.mk M.ρ) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact Submodule.mem_map.mpr ⟨e i, LinearMap.mem_range.mpr
            ⟨single i (MonoidAlgebra.single 1 1), by simpa using hπ i 1 1⟩, he i⟩
        obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp (hmap hx)
        have hxw : x - w ∈ Coinvariants.ker M.ρ := (Coinvariants.mk_eq_iff M.ρ).mp hwx.symm
        rw [show x = w + (x - w) by abel]
        exact Submodule.add_mem_sup hw hxw
    exact LinearMap.range_eq_top.mp hr

  let lam : M.V →ₗ[k] (ι →₀ k) := b.repr.toLinearMap ∘ₗ Coinvariants.mk M.ρ
  let s : (ι →₀ k) →ₗ[k] (ι →₀ k[G]) := Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1)
  have hlam : ∀ y, y - s (lam (π.hom y)) ∈ Coinvariants.ker (Representation.free k G ι) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem h₁ h₂
    | single i a =>
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a₁ a₂ h₁ h₂ =>
        rw [Finsupp.single_add, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem h₁ h₂
      | single g r =>
        refine Coinvariants.mem_ker_of_eq g (single i (MonoidAlgebra.single 1 r)) _ ?_
        rw [hπ]
        simp [lam, s, he]
  have hker : ∀ x, π.hom x = 0 → x ∈ Coinvariants.ker (Rep.free k G ι).ρ := fun x hx => by
    simpa [hx] using hlam x

  have hinj : Function.Injective π.hom :=
    injective_of_isZero_groupHomology_one hG π hsurj hM hker
  let eqv : (Representation.free k G ι).Equiv M.ρ :=
    Representation.Equiv.mk (LinearEquiv.ofBijective π.hom.toLinearMap ⟨hinj, hsurj⟩) fun g =>
      LinearMap.ext fun y => Rep.hom_comm_apply π g y
  exact ⟨ι, ⟨Rep.mkIso eqv⟩⟩
end GroundTheory.GroupCoh

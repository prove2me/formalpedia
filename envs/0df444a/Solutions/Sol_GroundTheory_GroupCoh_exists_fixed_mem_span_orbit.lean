-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_fixed_mem_span_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:57.963122+00:00
-- url     : https://prove2.me/submissions/ccb7f09b-9cb0-4e8f-9071-a62dc79fc0e7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed

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
open Representation
variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) (ρ : Representation k G V) {m : V}
    (hm : m ≠ 0) :
    ∃ v ∈ Submodule.span k (Set.range fun g : G => ρ g m), v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  classical
  have hp : ∀ x : V, p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  let cast : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  let f : (G → ZMod p) →+ V :=
    { toFun := fun c => ∑ g, cast (c g) • ρ g m
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  have hf : ∀ c, f c = ∑ g, cast (c g) • ρ g m := fun _ => rfl
  have hstab : ∀ (h : G) (c : G → ZMod p), ρ h (f c) = f (fun g => c (h⁻¹ * g)) := by
    intro h c
    rw [hf, hf, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp [map_mul, Module.End.mul_apply]
  have hmem : ∀ (h : G) (x : V), x ∈ f.range → ρ h x ∈ f.range := by
    rintro h x ⟨c, rfl⟩
    exact ⟨fun g => c (h⁻¹ * g), (hstab h c).symm⟩
  have : Finite f.range :=
    Finite.of_injective (fun x : f.range => (⟨x.1, AddMonoidHom.mem_range.mp x.2⟩ : Set.range f))
      fun a b h => Subtype.ext (congrArg Subtype.val h)
  let : MulAction G f.range :=
    { smul := fun h x => ⟨ρ h x, hmem h x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ρ 1 (x : V) = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ρ (a * b) (x : V) = ρ a (ρ b x)
        rw [map_mul, Module.End.mul_apply]) }
  have hm' : m ∈ f.range := ⟨Pi.single 1 1, by
    rw [hf, Fintype.sum_eq_single (1 : G) (fun g hg => by simp [hg])]
    simp⟩
  have horder : addOrderOf (⟨m, hm'⟩ : f.range) = p :=
    addOrderOf_eq_prime (Subtype.ext (by simpa using hp m))
      (fun h => hm (congrArg Subtype.val h))
  have hdvd : p ∣ Nat.card f.range := by
    have := addOrderOf_dvd_natCard (⟨m, hm'⟩ : f.range)
    rwa [horder] at this
  have h0 : (0 : f.range) ∈ MulAction.fixedPoints G f.range := fun g => Subtype.ext (by
    change ρ g 0 = 0
    simp)
  obtain ⟨b, hb, hb0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point f.range hdvd h0
  refine ⟨b.1, ?_, fun h => hb0 (Subtype.ext h.symm), fun g => congrArg Subtype.val (hb g)⟩
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.mp b.2
  rw [← hc, hf]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
end GroundTheory.GroupCoh

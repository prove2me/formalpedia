-- Prove2me | solution 1 for GroundTheory.GroupCoh.eq_top_of_sup_coinvariantsKer_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:22.372094+00:00
-- url     : https://prove2.me/submissions/1e65cc8a-7e7e-4297-90c7-e07c71228471

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Theorems.Thm_GroundTheory_GroupCoh_exists_fixed_mem_span_orbit

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
variable {k G V : Type*} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g : G, W ≤ W.comap (ρ g)) (h : W ⊔ Coinvariants.ker ρ = ⊤) :
    W = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
  obtain ⟨v, hvspan, hv0, hvfix⟩ := exists_fixed_mem_span_orbit hG ρ.dual hf0
  have hd : ∀ (g : G) (φ : Module.Dual k V) (x : V), ρ.dual g φ x = φ (ρ g⁻¹ x) :=
    fun _ _ _ => rfl

  have hvW : W ≤ LinearMap.ker v := by
    have hle : Submodule.span k (Set.range fun g : G => ρ.dual g f) ≤ W.dualAnnihilator := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      intro w hw
      rw [hd]
      exact hWf (hW g⁻¹ hw)
    intro w hw
    exact (Submodule.mem_dualAnnihilator v).mp (hle hvspan) w hw

  have hvI : Coinvariants.ker ρ ≤ LinearMap.ker v := by
    rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    have := congrArg (fun φ : Module.Dual k V => φ x) (hvfix g⁻¹)
    simp only [hd, inv_inv] at this
    simp [this]
  apply hv0
  ext x
  have hx : x ∈ W ⊔ Coinvariants.ker ρ := h ▸ Submodule.mem_top
  exact (sup_le hvW hvI) hx
end GroundTheory.GroupCoh

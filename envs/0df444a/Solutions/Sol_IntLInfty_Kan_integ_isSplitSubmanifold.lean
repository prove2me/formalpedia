-- Prove2me | solution 1 for IntLInfty.Kan.integ_isSplitSubmanifold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:03:17.110171+00:00
-- url     : https://prove2.me/submissions/bcc7f47a-dd4d-4269-b34d-b9690f4e8964

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_volterra_chart
import Theorems.Thm_IntLInfty_Kan_volterra_chart_contraction
import Theorems.Thm_IntLInfty_Kan_splitSubmanifold_of_volterra

set_option autoImplicit false

open scoped ContDiff

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) (m : ℕ) :
    IsSplitSubmanifold (integ r δ S m) := by
  obtain ⟨G, H, hGH⟩ := volterra_chart r hr L δ
  obtain ⟨hIs, hC, hGc, hHid, -, -, hint, -⟩ := hGH S hcl
  haveI := hC m
  exact splitSubmanifold_of_volterra (G S m) (hGc m) (H S m) (hHid m) _ (hint m)
    (fun x _ => volterra_chart_contraction r hr L δ S hcl (G S) hIs hGc m x)

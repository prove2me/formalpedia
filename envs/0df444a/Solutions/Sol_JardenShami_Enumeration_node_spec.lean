-- Prove2me | solution 1 for JardenShami.Enumeration.node_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:06.950176+00:00
-- url     : https://prove2.me/submissions/97b52125-5f97-47ab-80ce-4cbd484a0ad5

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_zero_lt_ord_lev

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
namespace Enumeration
theorem _root_.solution (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β δ : Kappa κ} (h : β ≤ δ) :
    ht (e.node C β δ h) = β ∧ e.node C β δ h ≤ e.t δ 0 := by
  unfold Enumeration.node
  split_ifs with hβ
  · obtain ⟨hi, hle⟩ := hC β δ hβ
    exact ⟨e.ht_t (Kappa.coe_lt_ord β) hi, hle⟩
  · obtain rfl : β = δ := le_antisymm h (not_lt.1 hβ)
    exact ⟨e.ht_t (Kappa.coe_lt_ord β) (zero_lt_ord_lev hT (Kappa.coe_lt_ord β)), le_rfl⟩
end Enumeration
end JardenShami

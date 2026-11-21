-- Prove2me | solution 1 for JardenShami.two_power_lt_of_treeExp_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:30.629243+00:00
-- url     : https://prove2.me/submissions/01b19d45-a118-4142-bb23-68b817a2f4a4

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_mk_lim_le_treeExp
import Theorems.Thm_JardenShami_height_binTree
import Theorems.Thm_JardenShami_mk_binTree_le
import Theorems.Thm_JardenShami_two_power_le_mk_lim_binTree
import Theorems.Thm_JardenShami_Kappa_mk_eq


set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}} (hreg : κ.IsRegular)
    (h : ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) :
    ∀ ν < κ, 2 ^ ν < κ := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases lt_or_ge ν ℵ₀ with hfin | hinf
  · exact (Cardinal.power_lt_aleph0 (by exact_mod_cast Cardinal.natCast_lt_aleph0 (n := 2))
      hfin).trans_le hreg.aleph0_le
  · have hcard : #(binTree ν) < κ := by
      refine mk_binTree_le.trans_lt (Cardinal.sum_lt_of_isRegular hreg ?_ fun β => ?_)
      · rwa [Kappa.mk_eq]
      · have hβ : #(Set.Iio β) < ν := by
          have := Cardinal.mk_Iio_lt β (by rw [Kappa.mk_eq, Ordinal.type_toType])
          rwa [Kappa.mk_eq] at this
        exact IH _ hβ (hβ.trans hν)
    calc 2 ^ ν ≤ #(Lim (binTree ν)) := two_power_le_mk_lim_binTree hinf
      _ ≤ treeExp (max ν #(binTree ν)) ν := mk_lim_le_treeExp height_binTree (le_max_right _ _)
      _ < κ := h _ _ hinf (le_max_left _ _) (max_lt hν hcard)
end JardenShami

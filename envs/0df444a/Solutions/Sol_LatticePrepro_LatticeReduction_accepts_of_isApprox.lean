-- Prove2me | solution 1 for LatticePrepro.LatticeReduction.accepts_of_isApprox
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:05.728262+00:00
-- url     : https://prove2.me/submissions/f7c51650-a6d0-4464-84a0-3dd907fb1974

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Conversions_SearchTest

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.LatticeReduction end LatticePrepro.LatticeReduction

namespace LatticePrepro

namespace PNorm

lemma one_le_s (pn : PNorm) : 1 ≤ pn.s := by
  cases pn with
  | fin p hp => exact le_min hp (by norm_num)
  | inf => norm_num [PNorm.s]

lemma norm_nonneg {M : Type} [Fintype M] (pn : PNorm) (v : M → ℝ) : 0 ≤ pn.norm v := by
  cases pn with
  | fin p hp =>
      show 0 ≤ (∑ i, |v i| ^ p) ^ (1 / p)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _
  | inf =>
      show 0 ≤ ⨆ i, |v i|
      exact Real.iSup_nonneg fun i => abs_nonneg _

end PNorm

end LatticePrepro

namespace LatticePrepro

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (x : X)

lemma dist_nonneg (v : Λ.M → ℤ) : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _

lemma bddBelow_range_dist : BddBelow (Set.range fun v : Λ.lattice => Λ.dist pn x v) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact Λ.dist_nonneg pn x v⟩

theorem latticeDist_le {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) :
    Λ.latticeDist pn x ≤ Λ.dist pn x v :=
  ciInf_le (Λ.bddBelow_range_dist pn x) ⟨v, hv⟩

theorem latticeDist_le_of_exists {R : ℝ} (h : ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R) :
    Λ.latticeDist pn x ≤ R := by
  obtain ⟨v, hv, hvR⟩ := h
  exact (Λ.latticeDist_le pn x hv).trans hvR

end LatticeFamily

end LatticePrepro

namespace LatticePrepro

namespace LatticeReduction

variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)

/-- **Lemma 5.2 for lattices, YES instances**: if `16 · f^s ≤ g`, every `f`-approximate solution
to a YES instance is accepted. -/
private theorem accepts_of_isApprox {f : ℝ} (hf : 0 ≤ f) (hgf : 16 * f ^ pn.s ≤ g) {x : X}
    (hx : L.IsYes x) {v : Red.Λ.M → ℤ} (hv : Red.IsApprox f x v) : Red.Accepts x v := by
  refine ⟨hv.1, ?_⟩
  have hR : (0 : ℝ) < Red.R := by exact_mod_cast Red.one_le_R
  have hD : (0 : ℝ) ≤ L.numBlocks := by positivity
  have hs : 0 ≤ pn.s := by linarith [pn.one_le_s]
  -- `dist ≤ f · dist(t_x, Λ) ≤ f · R`
  have hdist : Red.Λ.dist pn x v / Red.R ≤ f := by
    rw [div_le_iff₀ hR]
    calc Red.Λ.dist pn x v ≤ f * Red.Λ.latticeDist pn x := hv.2
      _ ≤ f * Red.R := by
          gcongr
          exact Red.Λ.latticeDist_le_of_exists pn x (Red.yes x hx)
  have h : (Red.weight x v : ℝ) ≤ (g : ℝ) * L.numBlocks :=
    calc (Red.weight x v : ℝ) ≤ 16 * L.numBlocks * (Red.Λ.dist pn x v / Red.R) ^ pn.s :=
          Red.weight_le x v hv.1
      _ ≤ 16 * L.numBlocks * f ^ pn.s := by
          gcongr
          · exact div_nonneg (Red.Λ.dist_nonneg pn x v) hR.le
      _ = (16 * f ^ pn.s) * L.numBlocks := by ring
      _ ≤ g * L.numBlocks := by gcongr
  exact_mod_cast h

end LatticeReduction

end LatticePrepro

open LatticePrepro
open LatticePrepro.LatticeReduction
variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)
theorem solution {f : ℝ} (hf : 0 ≤ f) (hgf : 16 * f ^ pn.s ≤ g) {x : X}
    (hx : L.IsYes x) {v : Red.Λ.M → ℤ} (hv : Red.IsApprox f x v) : Red.Accepts x v :=
  @LatticePrepro.LatticeReduction.accepts_of_isApprox p _ X L g pn Red f hf hgf x hx v hv

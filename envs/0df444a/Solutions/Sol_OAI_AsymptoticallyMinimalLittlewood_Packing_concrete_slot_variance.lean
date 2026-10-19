-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:27:09.180716+00:00
-- url     : https://prove2.me/submissions/0ab22ba1-3a0e-472e-a497-493aaa43ad0b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotGraph.lean:L259-L288
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_averaged_density_variance
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_catalog_chunk_system

-- ---- from OAI.Analysis.Littlewood.Chunks ----
namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

variable {r : ℕ}
lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- from OAI.Analysis.Littlewood.SlotGraph ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uK uV uJ

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
open Nibble
section SlotGraph
variable {I : Type uI} {K : Type uK} {V : Type uV} [Fintype I] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

end SlotGraph
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
section RandomMatching
variable {I : Type} [Fintype I] [DecidableEq I]

end RandomMatching
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
attribute [local instance] Classical.propDecidable

lemma concrete_slot_variance {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (i₀ : Fin r) (hK : 0<K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      3*(2*((r-1 : ℕ)*(q-(catalogSet d R K q).card : ℝ)/q+
          2*((r-1 : ℕ) : ℝ)^2*(shortResidues q (R*periodLength (oddLengths d))).card/q)+
        ((r-1 : ℕ) : ℝ)^2*
          (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ)/q) := by
  have hL := periodLength_pos d i₀
  have : Nonempty (Fin (periodLength (oddLengths d))) := ⟨⟨0,hL⟩⟩
  obtain ⟨chunk,hchunk,hhit,hB,hcollision⟩ := catalog_chunk_system d R K q i₀ hK hq
  have h := averaged_density_variance (g i)
    (fun j : {j : Fin r // j≠i} ↦ g j) (hg i) (fun j ↦ hg j)
    (fun j ↦ hpair i j (Ne.symm j.2))
    (fun j l hjl ↦ hpair j l (fun h ↦ hjl (Subtype.ext h)))
    (catalogSet d R K q) (shortResidues q (R*periodLength (oddLengths d))) chunk hcollision
    (fun j t ω ↦ slotHit d R K q j ω t) (fun j ↦ hhit j)
    (B := (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ))
    (fun k ↦ by exact_mod_cast hB k)
  have hc : Fintype.card {j : Fin r // j≠i}=r-1 := by
    simp [Fintype.card_subtype_compl]
  convert h using 1 <;>
    simp only [slotDensity, hc, Fintype.card_prod, Fintype.card_fin,Fintype.card_bool,ZMod.card,
      Nat.cast_mul, Nat.cast_ofNat, mul_comm (periodLength (oddLengths d) : ℝ) 2]

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset Nibble
attribute [local instance] Classical.propDecidable


theorem solution.{uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance.{uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance.{uV}

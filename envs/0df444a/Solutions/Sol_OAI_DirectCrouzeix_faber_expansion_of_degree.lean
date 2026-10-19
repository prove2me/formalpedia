-- Prove2me | solution 1 for OAI.DirectCrouzeix.faber_expansion_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:03:14.47302+00:00
-- url     : https://prove2.me/submissions/2bc5e51d-5c67-4a12-bc3f-2e2b5350a367

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DomainCore.lean:L119-L151
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.faber_expansion_of_degree. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy

-- ---- from OAI.Analysis.DirectCrouzeix.DomainCore ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem faber_expansion_of_degree {m : ℕ} (hm : 0 < m)
    (b : ℕ → Polynomial ℂ) (hb : ∀ k, (b k).degree = k) (G : MatrixPolynomial m) :
    ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ), G = faberPolynomial b C := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let S : Polynomial.Sequence (Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun k => scalarMatrixPolynomial (b k),fun k => by
      rw [scalarMatrixPolynomial,Polynomial.degree_map,hb]⟩
  have hunit (k : ℕ) : IsUnit (S k).leadingCoeff := by
    change IsUnit (scalarMatrixPolynomial (b k)).leadingCoeff
    rw [scalarMatrixPolynomial,Polynomial.leadingCoeff_map]
    apply IsUnit.map
    apply isUnit_iff_ne_zero.mpr
    apply Polynomial.leadingCoeff_ne_zero.mpr
    apply Polynomial.degree_ne_bot.mp
    rw [hb]
    exact WithBot.coe_ne_bot
  let N := G.natDegree+1
  have himage : Set.range (fun k : Fin N => S k) = S '' Set.Iio N := by
    ext p
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨k,k.isLt,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  have hG : G ∈ Submodule.span (Matrix (Fin m) (Fin m) ℂ) (Set.range (fun k : Fin N => S k)) := by
    rw [himage,S.span_degreeLT (fun k _ => hunit k),Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt G.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self G.natDegree)
  obtain ⟨C,hC⟩ := (Submodule.mem_span_range_iff_exists_fun (Matrix (Fin m) (Fin m) ℂ)).mp hG
  refine ⟨N,C,?_⟩
  rw [← hC]
  simp only [faberPolynomial,Polynomial.smul_eq_C_mul]
  rfl

end DirectCrouzeix

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.faber_expansion_of_degree := @_root_.OAI.DirectCrouzeix.faber_expansion_of_degree

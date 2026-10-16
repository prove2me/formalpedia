-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.beam_product_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:03:51.230428+00:00
-- url     : https://prove2.me/submissions/f16fc676-48f7-4363-952b-51f477033952

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/Fock/Beam.lean:L854-L885
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.beam_product_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam

-- ---- from OAI.MathematicalPhysics.Fock.Beam ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial

namespace FischerBeam
variable {J : Type*} [Fintype J] [DecidableEq J]

end FischerBeam

namespace FischerBeam

end FischerBeam

namespace FischerBeam

end FischerBeam

namespace FischerBeam

end FischerBeam

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace BlockUnitary

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

end BlockUnitary

namespace BlockUnitary
variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BlockUnitary

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace FischerBeam
open MvPolynomial

end FischerBeam

namespace EntropyPhotonNumber
open FischerBeam

theorem beam_product_lower {n : ℕ} (j : Fin n) (f : Fin n → ℕ → ℕ → ℕ → ℕ → ℝ)
    (k e a b : NumberIndex n) (u c s : ℝ)
    (h : u*f j (k j+1) (e j) (a j) (b j) =
      c*f j (k j) (e j) (a j-1) (b j)+s*f j (k j) (e j) (a j) (b j-1)) :
    u*(∏ i, f i (Function.update k j (k j+1) i) (e i) (a i) (b i)) =
      c*(∏ i, f i (k i) (e i) (Function.update a j (a j-1) i) (b i))+
      s*(∏ i, f i (k i) (e i) (a i) (Function.update b j (b j-1) i)) := by
  classical
  let R := ∏ i ∈ Finset.univ.erase j, f i (k i) (e i) (a i) (b i)
  have h₁ : (∏ i, f i (Function.update k j (k j+1) i) (e i) (a i) (b i)) =
      f j (k j+1) (e j) (a j) (b j)*R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have h₂ : (∏ i, f i (k i) (e i) (Function.update a j (a j-1) i) (b i)) =
      f j (k j) (e j) (a j-1) (b j)*R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have h₃ : (∏ i, f i (k i) (e i) (a i) (Function.update b j (b j-1) i)) =
      f j (k j) (e j) (a j) (b j-1)*R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [h₁, h₂, h₃, ← mul_assoc, h]
  ring

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam
variable {n : ℕ}

end EntropyPhotonNumber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open FischerBeam


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.beam_product_lower := @_root_.OAI.EntropyPhotonNumber.beam_product_lower

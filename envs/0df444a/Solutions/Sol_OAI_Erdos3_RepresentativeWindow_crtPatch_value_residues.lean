-- Prove2me | solution 1 for OAI.Erdos3.RepresentativeWindow.crtPatch_value_residues
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:08:48.306996+00:00
-- url     : https://prove2.me/submissions/7fdd7612-4642-4ca8-997a-5f4f61e5289c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem ofCoordinates_center (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (t : σ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ((ofCoordinates P hP).slots t).center x i = aeval t (P i) := by
  simp only [slots, ofCoordinates, MvPolynomial.comp_aeval_apply, aeval_X, Sum.elim_inl]

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open _root_.MvPolynomial

variable {X : Type*} {s d : ℕ}

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open _root_.MvPolynomial

variable {σ τ : Type*} {s : ℕ}

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

theorem patch_term {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ) :
    (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) =
      w.value (aeval t P - (b 0 : ℝ)) := by
  simp only [patch, PolynomialPatch.ofCoordinates, kernel, TriangularSlots.residual,
    PolynomialSlots.ofCoordinates_center, map_sub, aeval_C, Algebra.algebraMap_self_apply]
  congr 1
  ring

theorem patch_value {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) (t : σ → ℝ) :
    (w.patch s hs P hP).value t = w.value (Int.fract (aeval t P)) := by
  change (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
    (((w.patch s hs P hP).form.slots t).residual b)) = _
  simp_rw [w.patch_term s hs P hP t]
  rw [tsum_eq_single (fun _ : Fin 1 => ⌊aeval t P⌋)]
  · rfl
  · intro b hb
    by_contra h
    obtain ⟨h0, h1⟩ := w.interior _ h
    have hfloor : ⌊aeval t P⌋ = b 0 := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    apply hb
    funext i
    fin_cases i
    exact hfloor.symm

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtIntegerRepresentative_cast (u : J → ℤ) :
    (crtIntegerRepresentative N hN u : ZMod (∏ j, N j)) =
      (ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j))) := by
  let E := ZMod.prodEquivPi N hN
  have hcoeff (j : J) : (crtIntegerCoefficient N hN j : ZMod (∏ j, N j)) =
      E.symm (Pi.single j (1 : ZMod (N j))) := by
    simp only [crtIntegerCoefficient, Int.cast_natCast, ZMod.natCast_zmod_val, E]
  calc
    _ = ∑ j, E.symm (Pi.single j (1 : ZMod (N j))) * (u j : ZMod (∏ j, N j)) := by
      simp only [crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, hcoeff]
    _ = E.symm (∑ j, Pi.single j (1 : ZMod (N j)) * (u j : (j : J) → ZMod (N j))) := by
      simp only [map_sum, map_mul, map_intCast]
    _ = _ := by
      congr 1
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same, one_mul]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij.symm, zero_mul]
      · simp

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_eval (u : J → ℤ) :
    aeval (fun j => (u j : ℝ)) (crtRepresentativePolynomial N hN) =
      (crtIntegerRepresentative N hN u : ℝ) / (∏ i, N i : ℕ) := by
  simp only [crtRepresentativePolynomial, map_sum, map_smul, aeval_X,
    smul_eq_mul, crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRepresentativeFraction
namespace OAI

section

namespace Erdos3

theorem integer_fraction_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    Int.fract ((a : ℝ) / N) = (((a : ZMod N).val : ℝ) / N) := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  exact congrArg (fun z : ℤ => (z : ℝ) / N) (ZMod.val_intCast a).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport
namespace OAI

section

namespace Erdos3.RepresentativeWindow

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtPatch_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) (u : J → ℤ) :
    (w.crtPatch N hN s hs).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) := by
  rw [crtPatch, w.patch_value, crtRepresentativePolynomial_eval,
    integer_fraction_eq_zmod_val, crtIntegerRepresentative_cast]

theorem crtPatch_value_residues [∀ j, NeZero (N j)] (w : RepresentativeWindow)
    (s : ℕ) (hs : 1 ≤ s) (u : (j : J) → ZMod (N j)) :
    (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) := by
  have h := w.crtPatch_value N hN s hs (fun j => ((u j).val : ℤ))
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h

end Erdos3.RepresentativeWindow

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.RepresentativeWindow.crtPatch_value_residues.{u_1} := @OAI.Erdos3.RepresentativeWindow.crtPatch_value_residues.{u_1}

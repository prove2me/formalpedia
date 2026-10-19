-- Prove2me | solution 1 for MIPRE.Verifier.hasPerfectPCC_of_congr_at
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:37:49.984847+00:00
-- url     : https://prove2.me/submissions/97aa29a0-2406-4ac1-be8b-af5439cacd6c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/VerifierIndexTransport.lean (solution of MIPRE.Verifier.hasPerfectPCC_of_congr_at);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_VerifierIndexTransport
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Verifier
noncomputable section
open CL
theorem toBits_dimensionEquiv {s t : ℕ} (h : s = t) (x : Fin s → 𝔽₂) :
    toBits (dimensionEquiv h x) = toBits x := by
  subst t
  rfl
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
theorem clDist_dimensionEquiv {s t ℓ : ℕ} (h : s = t)
    (L R : CLFun 𝔽₂ (Fin s) ℓ) (L' R' : CLFun 𝔽₂ (Fin t) ℓ)
    (hL : HEq L L') (hR : HEq R R') (x y : Fin s → 𝔽₂) :
    clDist L'.eval R'.eval (dimensionEquiv h x) (dimensionEquiv h y) =
      clDist L.eval R.eval x y := by
  subst t
  cases eq_of_heq hL
  cases eq_of_heq hR
  rfl
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem game_mu_dimensionEquiv (h : SamplerAgreement V W n) (x y : V.Questions n) :
    (W.game n T).μ (dimensionEquiv h.dimension x) (dimensionEquiv h.dimension y) =
      (V.game n T).μ x y :=
  clDist_dimensionEquiv h.dimension _ _ _ _ (h.presentation .alice) (h.presentation .bob) x y
end
end MIPRE.Verifier

namespace MIPRE.Verifier
noncomputable section
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem game_D_dimensionEquiv (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (x y : V.Questions n) (a b : Answers T) :
    (W.game n T).D (dimensionEquiv h.dimension x) (dimensionEquiv h.dimension y) a b =
      (V.game n T).D x y a b := by
  classical
  change decide (W.decider.Accepts n _ _ _ _) = decide (V.decider.Accepts n _ _ _ _)
  simp only [toBits_dimensionEquiv]
  exact decide_eq_decide.mpr (hD _ _ _ _).symm
end
end MIPRE.Verifier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Verifier
open CL
variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}
theorem _root_.solution (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by
  let e := dimensionEquiv h.dimension
  let e' := Equiv.prodCongr (Equiv.refl Bool) e.symm
  have hμ (p q : Bool × W.Questions n) :
      (W.doubledGame n T).μ p q = (V.doubledGame n T).μ (e' p) (e' q) := by
    change (if p.1 = false ∧ q.1 = true then (W.game n T).μ p.2 q.2 else 0) =
      if p.1 = false ∧ q.1 = true then (V.game n T).μ (e.symm p.2) (e.symm q.2) else 0
    have hh := game_mu_dimensionEquiv (T := T) h (e.symm p.2) (e.symm q.2)
    change (W.game n T).μ (e (e.symm p.2)) (e (e.symm q.2)) = _ at hh
    simpa only [Equiv.apply_symm_apply] using congrArg (fun r => if p.1 = false ∧ q.1 = true then r else 0) hh
  have hd (p q : Bool × W.Questions n) (a b : Answers T) :
      (W.doubledGame n T).D p q a b = (V.doubledGame n T).D (e' p) (e' q) a b := by
    change (if p.1 = false ∧ q.1 = true then (W.game n T).D p.2 q.2 a b else false) =
      if p.1 = false ∧ q.1 = true then (V.game n T).D (e.symm p.2) (e.symm q.2) a b else false
    have hh := game_D_dimensionEquiv h hD (e.symm p.2) (e.symm q.2) a b
    change (W.game n T).D (e (e.symm p.2)) (e (e.symm q.2)) a b = _ at hh
    simpa only [Equiv.apply_symm_apply] using congrArg (fun r => if p.1 = false ∧ q.1 = true then r else false) hh
  obtain ⟨R,hR,hv⟩ := hV
  exact ⟨R.relabel _ e' (.refl _), R.isPCC_relabel hR _ e' (.refl _) hμ,
    (R.value_relabel _ e' (.refl _) hμ hd).trans hv⟩
end MIPRE.Verifier

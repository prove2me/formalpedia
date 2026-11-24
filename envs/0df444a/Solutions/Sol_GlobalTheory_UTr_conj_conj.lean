-- Prove2me | solution 1 for GlobalTheory.UTr.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:48.204418+00:00
-- url     : https://prove2.me/submissions/540df841-e3e0-4530-880f-a3193d2f6fb6

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : Csr s)
open Polynomial Matrix
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : _root_.GlobalTheory.UTr.Csr s)
namespace GlobalTheory.UTr
namespace _root_.GlobalTheory.UTr
theorem _root_.solution (hs : ∀ b, s (s b) = b)
    (z : _root_.GlobalTheory.UTr.Alg P) :
    _root_.GlobalTheory.UTr.conj P (_root_.GlobalTheory.UTr.conj P z) = z := by
  set σ := _root_.GlobalTheory.UTr.conj P
  set γ := _root_.GlobalTheory.UTr.gamma P
  have hγ : ((γ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
      _root_.GlobalTheory.UTr.root P := rfl
  have hinv : σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
      _root_.GlobalTheory.UTr.root P := by
    have e : ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
        σ γ := (_root_.GlobalTheory.UTr.conj_root P).symm
    have h1 : σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) *
        ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = 1 := by
      calc _ = σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) *
            σ γ := by rw [← e]
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)
        = σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) *
          (((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) * γ) := by
          rw [Units.inv_mul, mul_one]
      _ = γ := by rw [← mul_assoc, h1, one_mul]
      _ = _root_.GlobalTheory.UTr.root P := hγ
  obtain ⟨q, rfl⟩ := _root_.GlobalTheory.UTr.exists_aeval_root P z
  induction q using Polynomial.induction_on with
  | C a => simp [σ, hs]
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, ih, aeval_X,
      _root_.GlobalTheory.UTr.conj_root, hinv]
end _root_.GlobalTheory.UTr
end GlobalTheory.UTr

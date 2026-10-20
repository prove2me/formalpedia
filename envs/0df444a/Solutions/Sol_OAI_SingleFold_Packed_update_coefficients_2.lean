-- Prove2me | solution 2 for OAI.SingleFold.Packed.update_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:04:15.544992+00:00
-- url     : https://prove2.me/submissions/a1c7b5ac-c89c-4355-bd51-3f997f6c21d1

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Packed.lean:L248-L279
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Packed.update_coefficients. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma digit_zero (B t : ℕ) : digit B 0 t=0 := by simp [digit]
lemma pack_cons (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=f 0+B*pack B k (fun t=>f (t+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros; ring
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_add (B k : ℕ) (f g : ℕ → ℕ) :
    pack B k (fun t=>f t+g t)=pack B k f+pack B k g := by simp [pack,add_mul,Finset.sum_add_distrib]
lemma digit_pack {B k : ℕ} (hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) (i : ℕ) :
    digit B (pack B k f) i=if i < k then f i else 0 := by
  induction k generalizing f i with
  | zero => simp [pack_zero,digit_zero]
  | succ k ih =>
    rw [pack_cons]
    cases i with
    | zero => simp [digit,Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hf 0 (by omega)),zero_add]
      simpa only [digit, Nat.add_lt_add_iff_right] using ih (fun t ht=>hf (t+1) (by omega)) i

lemma pack_injective {B k : ℕ} (hB : 0 < B) {f g : ℕ → ℕ}
    (hf : ∀t < k,f t < B) (hg : ∀t < k,g t < B) (he : pack B k f=pack B k g) :
    ∀t < k,f t=g t := by
  intro t ht
  have hh := congrArg (fun x=>digit B x t) he
  simpa [digit_pack hB hf,digit_pack hB hg,ht] using hh

lemma pack_shift (B k : ℕ) (f : ℕ → ℕ) :
    pack B (k+1) (fun t=>if t=0 then 0 else f (t-1))=B*pack B k f := by
  rw [pack_cons]
  simp
lemma pack_init (B k a : ℕ) (f : ℕ → ℕ) :
    pack B (k+1) (fun t=>if t=0 then a else f (t-1))=a+B*pack B k f := by
  rw [pack_cons]
  simp
lemma update_coefficients {B T m d : ℕ} (hB : 2*m ≤ B) (hd : d < m)
    (r a f : ℕ → ℕ) (hr : ∀t < T+1,r t < m) (ha : ∀t < T,a t ≤ 1) (hf : ∀t < T,f t ≤ 1)
    (he : pack B (T+1) r+B*pack B T f=d+B*(pack B T r+pack B T a)) :
    r 0=d ∧ ∀t < T,r (t+1)+f t=r t+a t := by
  have hpos : 0 < B := by omega
  let l := fun t=>r t+(if t=0 then 0 else f (t-1))
  let u := fun t=>if t=0 then d else r (t-1)+a (t-1)
  have he' : pack B (T+1) l=pack B (T+1) u := by
    dsimp [l,u]
    rw [pack_add,pack_shift]
    rw [pack_init B T d (fun u=>r u+a u),pack_add]
    exact he
  have hl : ∀t < T+1,l t < B := by
    intro t ht
    dsimp [l]
    split_ifs with ht0
    · have := hr t ht; omega
    · have hh := hr t ht
      have hh' := hf (t-1) (by omega)
      omega
  have hu : ∀t < T+1,u t < B := by
    intro t ht
    dsimp [u]
    split_ifs with ht0
    · omega
    · have hh := hr (t-1) (by omega)
      have hh' := ha (t-1) (by omega)
      omega
  have hh := pack_injective hpos hl hu he'
  refine ⟨by simpa [l,u] using hh 0 (by omega),?_⟩
  intro t ht
  simpa [l,u] using hh (t+1) (by omega)

end SingleFold.Packed

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Packed.update_coefficients := @_root_.OAI.SingleFold.Packed.update_coefficients

-- Prove2me | solution 1 for HardyCapset20261020.Cert.fast_orbit_block_sound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T17:06:05.883277+00:00
-- url     : https://prove2.me/submissions/0cb84125-5522-4873-91e5-c569eca100eb

import Definitions.Def_HardyCapsetFastOrbitVerifier20261021
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace HardyCapset20261020.Cert
theorem cast_mul_mod (a b : ℕ) :
    ((a*b%3 : ℕ) : ZMod 3) = (a : ZMod 3) * (b : ZMod 3) := by
  rw [ZMod.natCast_mod, Nat.cast_mul]

theorem cast_natGen (i : ℕ) (v : NatPoint) :
    castPoint (natGen i v) = genGet generators i (castPoint v) := by
  by_cases hi : i < 9
  · change castPoint (natGen (⟨i, hi⟩ : Fin 9).val v) =
      genGet generators (⟨i, hi⟩ : Fin 9).val (castPoint v)
    generalize (⟨i, hi⟩ : Fin 9) = ii
    fin_cases ii <;> funext j <;> fin_cases j <;> exact cast_mul_mod _ _
  · have hg : ¬ i < generators.size := by simpa [generators] using hi
    rw [show genGet generators i = AddEquiv.refl Point by simp [genGet, hg]]
    funext j
    change (natGen i v j : ZMod 3) = (v j : ZMod 3)
    simp only [natGen, dif_neg hi]

theorem cast_natWord (w : List ℕ) (v : NatPoint) :
    castPoint (natWord w v) = wordMap generators w (castPoint v) := by
  induction w with
  | nil => rfl
  | cons i rest ih =>
      rw [natWord, cast_natGen, ih]
      rfl

theorem fastOrbitBlock_sound (start packed len : ℕ)
    (h : fastOrbitBlockB start packed len = true)
    (k : ℕ) (hk : k < len) : OrbitCovered (start + k) := by
  have hc := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  have hh : (orbitRecord packed k).representative < 246 ∧
      (orbitRecord packed k).groupIndex < groupWords.size ∧
      ((orbitRecord packed k).factor = 1 ∨ (orbitRecord packed k).factor = 2) ∧
      (∀ j ∈ List.range 8,
        digit ((start+k)/3+1) j = ((orbitRecord packed k).factor *
          natWord groupWords[(orbitRecord packed k).groupIndex]!
          (rawDigits (entry representativeNormals (orbitRecord packed k).representative))
          ⟨j%8, Nat.mod_lt _ (by decide)⟩) % 3) ∧
      (start+k)%3 = ((orbitRecord packed k).factor *
        entry representativeLevels (orbitRecord packed k).representative) % 3 := by
    simpa only [fastOrbitEntryB, Bool.and_eq_true, decide_eq_true_eq,
      Bool.or_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] using hc
  let r := orbitRecord packed k
  let w := groupWords[r.groupIndex]!
  let v := rawDigits (entry representativeNormals r.representative)
  refine ⟨⟨r.representative, hh.1⟩, w, r.factor, ?_, ?_, ?_⟩
  · rcases hh.2.2.1 with he | he <;> norm_num [r, he] <;> decide
  · have hw : castPoint (natWord w v) =
        wordMap generators w (decode (entry representativeNormals r.representative)) :=
      cast_natWord w v
    rw [← hw]
    funext j
    have hj := hh.2.2.2.1 j.val (List.mem_range.mpr j.isLt)
    have hmod : j.val % 8 = j.val := Nat.mod_eq_of_lt j.isLt
    have he := congrArg (fun a : ℕ => (a : ZMod 3)) hj
    change (digit ((start+k)/3+1) j.val : ZMod 3) =
      (r.factor : ZMod 3) * (natWord w v j : ZMod 3)
    simpa only [ZMod.natCast_mod,
      Nat.cast_mul, hmod] using he
  · have he := congrArg (fun a : ℕ => (a : ZMod 3)) hh.2.2.2.2
    simpa only [ZMod.natCast_mod, Nat.cast_mul] using he
end HardyCapset20261020.Cert

open HardyCapset20261020.Cert
theorem solution (start packed len : Nat) (h : fastOrbitBlockB start packed len = true) (k : Nat) (hk : k < len) : OrbitCovered (start+k) := fastOrbitBlock_sound start packed len h k hk
#print axioms solution

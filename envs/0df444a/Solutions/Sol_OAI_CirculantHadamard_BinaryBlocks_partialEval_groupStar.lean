-- Prove2me | solution 1 for OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:51:20.168639+00:00
-- url     : https://prove2.me/submissions/da9e64cb-c072-4c64-8a4a-7e3f5b89cb8a

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryBlocks
universe uR uS
open CyclicRing
open scoped BigOperators
variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]
omit [StarRing R] [StarRing S] in
theorem pea_aux (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) (b : ZMod m) :
    (partialEval m φ z hz f).coeff b =
      ∑ j : ZMod 4, φ (f.coeff (j, b)) * z ^ j.val := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, add_mul]
  | single a r =>
    rw [partialEval_single]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single a.1]
    · by_cases h : a.2 = b
      · have : a = (a.1, b) := Prod.ext rfl h
        rw [if_pos h, if_pos this]
      · have : ¬ a = (a.1, b) := fun h' => h (congrArg Prod.snd h')
        rw [if_neg h, if_neg this, map_zero, zero_mul]
    · intro j _ hj
      have : ¬ a = (j, b) := fun h' => hj (congrArg Prod.fst h').symm
      rw [if_neg this, map_zero, zero_mul]
    · simp

theorem solution (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hchar : ∀ a : ZMod 4, z ^ (-a).val = star (z ^ a.val))
    (f : ProductElem R m) :
    partialEval m φ z hz (groupStar f) = ringStar (partialEval m φ z hz f) := by
  apply AddMonoidAlgebra.coeff_injective
  ext b
  rw [ringStar_apply, pea_aux, pea_aux, star_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod 4)) _ _ (fun j => ?_)
  simp only [Equiv.neg_apply, groupStar_apply, Prod.neg_mk, star_mul, hφ, hchar, star_star]
  ring

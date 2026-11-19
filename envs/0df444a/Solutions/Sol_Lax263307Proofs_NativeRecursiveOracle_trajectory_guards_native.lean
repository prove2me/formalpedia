-- Prove2me | solution 1 for Lax263307Proofs.NativeRecursiveOracle.trajectory_guards_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:53.337098+00:00
-- url     : https://prove2.me/submissions/b74ee910-3e59-4f76-91a7-8ab150647a70

import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Nat.Log
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces

namespace Lax109476.RationalFeasibility
end Lax109476.RationalFeasibility
namespace Lax109476Proofs.BinaryOptimization
end Lax109476Proofs.BinaryOptimization
namespace Lax109476Proofs.BinaryOptimizationBounds
end Lax109476Proofs.BinaryOptimizationBounds
namespace Lax109476Proofs.CertificateSystems
end Lax109476Proofs.CertificateSystems
namespace Lax109476Proofs.CoordinateOptimization
end Lax109476Proofs.CoordinateOptimization
namespace Lax109476Proofs.DeterminantBounds
end Lax109476Proofs.DeterminantBounds
namespace Lax109476Proofs.EllipsoidDeterminant
end Lax109476Proofs.EllipsoidDeterminant
namespace Lax109476Proofs.EllipsoidTermination
end Lax109476Proofs.EllipsoidTermination
namespace Lax109476Proofs.IterationBudget
end Lax109476Proofs.IterationBudget
namespace Lax109476Proofs.LexicographicBounds
end Lax109476Proofs.LexicographicBounds
namespace Lax109476Proofs.PointRecovery
end Lax109476Proofs.PointRecovery
namespace Lax109476Proofs.RamEllipsoidStoredBounds
end Lax109476Proofs.RamEllipsoidStoredBounds
namespace Lax109476Proofs.RamEllipsoidWordBounds
end Lax109476Proofs.RamEllipsoidWordBounds
namespace Lax109476Proofs.RamFrame
end Lax109476Proofs.RamFrame
namespace Lax109476Proofs.RamPadEntries
end Lax109476Proofs.RamPadEntries
namespace Lax109476Proofs.RamPrimitiveBounds
end Lax109476Proofs.RamPrimitiveBounds
namespace Lax109476Proofs.RamRecoveryData
end Lax109476Proofs.RamRecoveryData
namespace Lax109476Proofs.RamScalarFrame
end Lax109476Proofs.RamScalarFrame
namespace Lax109476Proofs.RationalFeasibility
end Lax109476Proofs.RationalFeasibility
namespace Lax109476Proofs.RationalMinima
end Lax109476Proofs.RationalMinima
namespace Lax109476Proofs.SmallFeasiblePoint
end Lax109476Proofs.SmallFeasiblePoint
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
namespace Lax263307Proofs.ConditioningDistribution
end Lax263307Proofs.ConditioningDistribution
namespace Lax263307Proofs.EntropyDecrease
end Lax263307Proofs.EntropyDecrease
namespace Lax263307Proofs.LightSeparators
end Lax263307Proofs.LightSeparators
namespace Lax263307Proofs.NativeDistanceEntries
end Lax263307Proofs.NativeDistanceEntries
namespace Lax263307Proofs.NativeMachineSegment
end Lax263307Proofs.NativeMachineSegment
namespace Lax263307Proofs.NativeUniformWordGuards
end Lax263307Proofs.NativeUniformWordGuards
namespace Lax455465.ShortPathFlow
end Lax455465.ShortPathFlow
namespace Lax455465Proofs.AcyclicFlowPath
end Lax455465Proofs.AcyclicFlowPath
namespace Lax455465Proofs.LargePotentialData
end Lax455465Proofs.LargePotentialData
namespace Lax455465Proofs.PathSubtraction
end Lax455465Proofs.PathSubtraction
namespace Lax455465Proofs.RamFlowData
end Lax455465Proofs.RamFlowData
namespace Lax455465Proofs.RationalParser
end Lax455465Proofs.RationalParser
namespace Lax455465Proofs.RegionHistory
end Lax455465Proofs.RegionHistory
namespace Lax455465Proofs.RegionInterval
end Lax455465Proofs.RegionInterval
namespace Lax455465Proofs.RegionRuntimeState
end Lax455465Proofs.RegionRuntimeState
namespace Lax455465Proofs.RoundingConstants
end Lax455465Proofs.RoundingConstants
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
namespace Lax759944Proofs.Legacy.RamPolytime
end Lax759944Proofs.Legacy.RamPolytime
namespace Lax808846.RamComputes
end Lax808846.RamComputes
namespace Lax808846Proofs.Machine
end Lax808846Proofs.Machine

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem member_bound (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x < 2 ^ bitSize xs:=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have:=member_size xs x hx; omega))

end Lax455465Proofs.WordSize

end

section

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_mono:Monotone depth:=by
  intro n m hnm
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hn:n≤ 1
    · rw [depth,if_pos hn]
      exact Nat.zero_le _
    · have hm:¬m≤ 1:=by omega
      rw [depth.eq_def n,if_neg hn,depth.eq_def m,if_neg hm]
      exact Nat.add_le_add_left (ih (2 * m / 3) (by omega)
        (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hnm))) 1

theorem balanced_decrease (n m:ℕ) (nontrivial:1 < n) (balanced:3 * m≤ 2 * n):
    depth m + 1≤ depth n:=by
  have hm:m≤ 2 * n / 3:=by omega
  have hdepth:=depth_mono hm
  rw [depth.eq_def n,if_neg (by omega)]
  omega

end Lax263307Proofs.RecursionDepth

end

section

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open EntropyDecrease

theorem candidate_complete (n r:ℕ) (A:Finset (Fin n)):
    A∈ candidates n r↔ A.card≤ r:=by
  constructor
  · intro h
    obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp h
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hm
    have hsub:=(List.mem_sublistsLen.mp hl).1
    have hlen:=(List.mem_sublistsLen.mp hl).2
    have hnd:=hsub.nodup (List.nodup_finRange n)
    rw [List.toFinset_card_of_nodup hnd,hlen]
    have:=List.mem_range.mp hj
    omega
  · intro hA
    let l:=(List.finRange n).filter fun v => decide (v∈ A)
    have hsub:List.Sublist l (List.finRange n):=List.filter_sublist
    have hnd:l.Nodup:=hsub.nodup (List.nodup_finRange n)
    have heq:l.toFinset=A:=by ext v; simp [l]
    have hlen:l.length=A.card:=by rw [← List.toFinset_card_of_nodup hnd,heq]
    apply List.mem_flatMap.mpr
    refine ⟨A.card,List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨l,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,heq⟩

end Lax263307Proofs.RationalConditioning

end

section

namespace Lax263307Proofs.CoordinateCatalog

open Lax263307.LinearRelaxation Lax263307.RationalConditioning Lax263307.CoordinateCatalog

theorem catalog_complete (n r:ℕ) (A:Coordinate n r):A∈ catalog n r:=by
  have hmem:A.val∈ sets n r:=
    List.mem_dedup.mpr ((Lax263307Proofs.RationalConditioning.candidate_complete n (r + 2) A.val).mpr A.property)
  apply List.mem_map.mpr
  exact ⟨⟨A.val,hmem⟩,List.mem_attach _ _,Subtype.ext rfl⟩

theorem catalog_two (n r:ℕ) (positive:0 < n):2≤ (catalog n r).length:=by
  let v:Fin n:= ⟨0,positive⟩
  let A:Coordinate n r:= ⟨∅,by simp⟩
  let B:Coordinate n r:= ⟨{v},by simp⟩
  have hne:A ≠ B:=by
    intro h
    have heq:(∅:Finset (Fin n))={v}:=congrArg Subtype.val h
    have hv:v∈ (∅:Finset (Fin n)):=heq.symm ▸ Finset.mem_singleton_self v
    exact Finset.notMem_empty v hv
  have hsub:({A,B}:Finset (Coordinate n r)) ⊆ (catalog n r).toFinset:=by
    intro C hC
    simp only [Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact List.mem_toFinset.mpr (Lax263307Proofs.CoordinateCatalog.catalog_complete n r A)
    · exact List.mem_toFinset.mpr (Lax263307Proofs.CoordinateCatalog.catalog_complete n r B)
  have hcard:=Finset.card_le_card hsub
  have hpair:({A,B}:Finset (Coordinate n r)).card=2:=by simp [hne]
  rw [hpair] at hcard
  exact hcard.trans (List.toFinset_card_le _)

end Lax263307Proofs.CoordinateCatalog

end

section

namespace Lax109476Proofs.RationalRounding

theorem grid_num_den_bound (k:ℤ) (D:ℕ) (hD:0 < D):
    ((k:ℚ) / D).num.natAbs≤ k.natAbs∧ ((k:ℚ) / D).den≤ D:=by
  obtain ⟨c,hnum,hden⟩:=Rat.exists_eq_mul_div_num_and_eq_mul_div_den k
    (d:=(D:ℤ)) (by exact_mod_cast ne_of_gt hD)
  have hc:c ≠ 0:=by
    intro h
    rw [h,zero_mul] at hden
    have hDn:(D:ℤ) ≠ 0:=by exact_mod_cast ne_of_gt hD
    exact hDn hden
  have hcpos:0 < c.natAbs:=Int.natAbs_pos.mpr hc
  have hnumAbs:k.natAbs=c.natAbs * ((k:ℚ) / D).num.natAbs:=by
    simpa only [Int.natAbs_mul,Int.cast_natCast] using congrArg Int.natAbs hnum
  have hdenAbs:D=c.natAbs * ((k:ℚ) / D).den:=by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,Int.cast_natCast] using
      congrArg Int.natAbs hden
  constructor
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).num.natAbs:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hnumAbs.symm
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).den:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hdenAbs.symm

theorem roundDown_le (q:ℚ) (D:ℕ) (hD:0 < D):roundDown q D≤ q:=by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).mpr
  exact Int.floor_le _

theorem lt_roundDown_add (q:ℚ) (D:ℕ) (hD:0 < D):
    q < roundDown q D + 1 / D:=by
  have hp:(0:ℚ) < D:=by exact_mod_cast hD
  unfold roundDown
  rw [← add_div,lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

theorem roundDown_error (q:ℚ) (D:ℕ) (hD:0 < D):
    0≤ (q:ℝ) - (roundDown q D:ℝ)∧
      (q:ℝ) - (roundDown q D:ℝ) < 1 / (D:ℝ):=by
  have h₁:(roundDown q D:ℝ)≤ (q:ℝ):=by
    exact_mod_cast roundDown_le q D hD
  have h₂:(q:ℝ) < (roundDown q D:ℝ) + 1 / (D:ℝ):=by
    have h:=(Rat.cast_lt (K:=ℝ)).mpr (lt_roundDown_add q D hD)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
  constructor <;> linarith

theorem roundDown_vector_error (n:ℕ) (x:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    (∑ i, ((x i:ℝ) - (roundDown (x i) D:ℝ)) ^ 2)≤
      (n:ℝ) * (1 / (D:ℝ)) ^ 2:=by
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  calc
    _≤ ∑ _i:Fin n, (1 / (D:ℝ)) ^ 2:=by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h₁,h₂⟩:=roundDown_error (x i) D hD
      nlinarith [show (0:ℝ) < 1 / (D:ℝ) by positivity]
    _=_:=by simp

theorem sqrtUpper_bounds (q:ℚ) (hq:0≤ q) (D:ℕ) (hD:0 < D):
    Real.sqrt (q:ℝ)≤ (sqrtUpper q D:ℝ)∧
      (sqrtUpper q D:ℝ) < Real.sqrt (q:ℝ) + 2 / (D:ℝ):=by
  let c:=Nat.ceil (q * (D:ℚ) ^ 2)
  let s:=Nat.sqrt c
  have hqR:(0:ℝ)≤ q:=by exact_mod_cast hq
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  have hcl:(q:ℝ) * (D:ℝ) ^ 2≤ c:=by
    have h:q * (D:ℚ) ^ 2≤ (c:ℚ):=Nat.le_ceil _
    have h':=(Rat.cast_le (K:=ℝ)).mpr h
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast] using h'
  have hcu:(c:ℝ) < (q:ℝ) * (D:ℝ) ^ 2 + 1:=by
    have h:(c:ℚ) < q * (D:ℚ) ^ 2 + 1:=
      Nat.ceil_lt_add_one (show (0:ℚ)≤ q * (D:ℚ) ^ 2 by positivity)
    have h':=(Rat.cast_lt (K:=ℝ)).mpr h
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_one] using h'
  have hsl:(s:ℝ) ^ 2≤ c:=by
    have h:s ^ 2≤ c:=Nat.sqrt_le' c
    have h':=(Nat.cast_le (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow] using h'
  have hsu:(c:ℝ) < ((s:ℝ) + 1) ^ 2:=by
    have h:c < (s + 1) ^ 2:=Nat.lt_succ_sqrt' c
    have h':=(Nat.cast_lt (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h'
  have hs:(0:ℝ)≤ s:=Nat.cast_nonneg _
  have hroot:=Real.sq_sqrt hqR
  have hrootpos:=Real.sqrt_nonneg (q:ℝ)
  have hsqr:(Real.sqrt (q:ℝ) * (D:ℝ)) ^ 2=(q:ℝ) * (D:ℝ) ^ 2:=by
    rw [mul_pow,hroot]
  have hl:Real.sqrt (q:ℝ) * D≤ (s:ℝ) + 1:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hcl,hsu,hsqr,ht,hs]
  have hu:(s:ℝ) + 1 < Real.sqrt (q:ℝ) * D + 2:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hsl,hcu,hsqr,ht,hs,
      sq_nonneg ((s:ℝ) - Real.sqrt (q:ℝ) * D)]
  have heq:(sqrtUpper q D:ℝ)=((s:ℝ) + 1) / D:=by
    simp [sqrtUpper,c,s]
  rw [heq]
  constructor
  · exact (le_div_iff₀ hDR).mpr hl
  · calc
      _ < (Real.sqrt (q:ℝ) * D + 2) / D:=
        (div_lt_div_iff_of_pos_right hDR).mpr hu
      _=_:=by field_simp

end Lax109476Proofs.RationalRounding

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem size_mul_le (a b:ℕ):Nat.size (a * b)≤ Nat.size a + Nat.size b:=by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

end Lax109476Proofs.RationalSizeBounds

end

section

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_cons (n:ℕ) (x:List ℕ):
    bitSize (n::x)=Nat.size n + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len]
  omega

theorem bitSize_nil:bitSize []=0:=rfl

theorem rational_size_upper (q:ℚ):
    bitSize (encodeRational q)≤ 4 + Nat.size q.num.natAbs + Nat.size q.den:=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  split_ifs <;> norm_num [Nat.size] <;> omega

end Lax109476Proofs.EncodingSize

end

section

namespace Lax109476Proofs.EllipsoidStep

noncomputable def centralCutForm (n r t:ℝ):ℝ:=
  (n + 1) ^ 2 / n ^ 2 * (t + 1 / (n + 1)) ^ 2 +
    (n ^ 2 - 1) / n ^ 2 * (r - t ^ 2)

theorem centralCutForm_le_one (n r t:ℝ) (hn:2≤ n)
    (hr:r≤ 1) (ht₁:-1≤ t) (ht₂:t≤ 0):
    centralCutForm n r t≤ 1:=by
  have hnpos:0 < n:=by linarith
  have hnzero:n ≠ 0:=ne_of_gt hnpos
  have hnplus:n + 1 ≠ 0:=by linarith
  have hid:centralCutForm n r t =
      ((n ^ 2 - 1) * r + 2 * (n + 1) * t * (t + 1) + 1) / n ^ 2:=by
    unfold centralCutForm
    field_simp
    ring
  rw [hid]
  apply (div_le_one (sq_pos_of_pos hnpos)).mpr
  have hcoeff:0≤ n ^ 2 - 1:=by nlinarith
  have hrad:=mul_le_mul_of_nonneg_left hr hcoeff
  have htprod:t * (t + 1)≤ 0:=
    mul_nonpos_of_nonpos_of_nonneg ht₂ (by linarith)
  have hterm:2 * (n + 1) * (t * (t + 1))≤ 0:=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) htprod
  nlinarith

noncomputable def determinantFactor (n:ℕ):ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) ^ (n - 1) *
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2

theorem determinantFactor_pos (n:ℕ) (hn:2≤ n):0 < determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  unfold determinantFactor
  apply mul_pos
  · apply pow_pos
    apply div_pos <;> nlinarith
  · apply sq_pos_of_pos
    apply div_pos <;> linarith

theorem log_determinantFactor_le (n:ℕ) (hn:2≤ n):
    Real.log (determinantFactor n)≤ -1 / ((n:ℝ) + 1):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hdiff:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  let a:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let b:=(n:ℝ) / ((n:ℝ) + 1)
  have ha:0 < a:=div_pos (sq_pos_of_pos hnp) hdiff
  have hb:0 < b:=div_pos hnp hplus
  have hlogA:=Real.log_le_sub_one_of_pos ha
  have hlogB:=Real.log_le_sub_one_of_pos hb
  have hk:((n - 1:ℕ):ℝ)=(n:ℝ) - 1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have heqA:((n - 1:ℕ):ℝ) * (a - 1)=1 / ((n:ℝ) + 1):=by
    rw [hk]
    dsimp [a]
    field_simp
    ring
  have heqB:2 * (b - 1)=-2 / ((n:ℝ) + 1):=by
    dsimp [b]
    field_simp
    ring
  have hA:=mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (n - 1))
  have hB:=mul_le_mul_of_nonneg_left hlogB (show (0:ℝ)≤ 2 by norm_num)
  rw [heqA] at hA
  rw [heqB] at hB
  change Real.log (a ^ (n - 1) * b ^ 2)≤ _
  rw [Real.log_mul (ne_of_gt (pow_pos ha _)) (ne_of_gt (sq_pos_of_pos hb)),
    Real.log_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _≤ 1 / ((n:ℝ) + 1) + -2 / ((n:ℝ) + 1):=add_le_add hA hB
    _=-1 / ((n:ℝ) + 1):=by ring

open Matrix

theorem enlarged_shrink_bound (n:ℕ) (hn:2≤ n) (δ:ℝ) (hδ:0≤ δ)
    (hδsmall:δ≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):
    (1 + δ) ^ n * Real.sqrt (determinantFactor n)≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hbase:0 < 1 + δ:=by linarith
  have hsqrt:=Real.sqrt_pos.mpr (determinantFactor_pos n hn)
  have hlogbase:Real.log (1 + δ)≤ δ:=by
    simpa using Real.log_le_sub_one_of_pos hbase
  have hlogshrink:Real.log (Real.sqrt (determinantFactor n))≤
      -1 / (2 * ((n:ℝ) + 1)):=by
    rw [Real.log_sqrt (le_of_lt (determinantFactor_pos n hn))]
    calc
      _≤ (-1 / ((n:ℝ) + 1)) / 2:=
        div_le_div_of_nonneg_right (log_determinantFactor_le n hn) (by norm_num)
      _=_:=by field_simp
  have hδmul:(n:ℝ) * δ≤ 1 / (4 * ((n:ℝ) + 1)):=by
    calc
      _≤ (n:ℝ) * (1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hδsmall (le_of_lt hnp)
      _=_:=by field_simp
  have hlogbound:Real.log ((1 + δ) ^ n * Real.sqrt (determinantFactor n))≤
      -1 / (4 * ((n:ℝ) + 1)):=by
    rw [Real.log_mul (ne_of_gt (pow_pos hbase n)) (ne_of_gt hsqrt),Real.log_pow]
    calc
      _≤ (n:ℝ) * δ + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add (mul_le_mul_of_nonneg_left hlogbase (le_of_lt hnp)) hlogshrink
      _≤ 1 / (4 * ((n:ℝ) + 1)) + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add hδmul (le_refl _)
      _=_:=by field_simp; ring
  simpa only [Real.exp_log (mul_pos (pow_pos hbase n) hsqrt)] using
    Real.exp_le_exp.mpr hlogbound

theorem iterated_shrink_bound (n:ℕ) (v:ℕ→ ℝ)
    (hstep:∀ k,v (k + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k)
    (k:ℕ):
    v k≤ Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0:=by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k:=hstep k
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) *
            (Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0):=
          mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
        _=_:=by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring

end Lax109476Proofs.EllipsoidStep

end

section

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

theorem symmetric_form {ι:Type} [Fintype ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (u v:ι→ ℝ):
    u ⬝ᵥ (A *ᵥ v)=v ⬝ᵥ (A *ᵥ u):=by
  have ht:Aᵀ=A:=(Matrix.isHermitian_iff_isSymm.mp hA).eq
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,ht,dotProduct_comm]

theorem quadratic_error_bound {n:ℕ} (E:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (hE:∀ i j, |E i j|≤ ε) (x:Fin n→ ℝ):
    |x ⬝ᵥ (E *ᵥ x)|≤ (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have hcs:(∑ i, |x i|) ^ 2≤ (n:ℝ) * (x ⬝ᵥ x):=by
    have h:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _:Fin n => (1:ℝ)) (fun i => |x i|)
    simpa [dotProduct,sq_abs,pow_two] using h
  calc
    _=|∑ i, ∑ j,x i * E i j * x j|:=by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    _≤ ∑ i, ∑ j, |x i * E i j * x j|:=by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _≤ ∑ i, ∑ j,ε * |x i| * |x j|:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _≤ |x i| * ε * |x j|:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _=_:=by ring
    _=ε * (∑ i, |x i|) ^ 2:=by
      simp only [Finset.mul_sum,Finset.sum_mul,pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤ ε * ((n:ℝ) * (x ⬝ᵥ x)):=mul_le_mul_of_nonneg_left hcs hε
    _=_:=by ring

theorem posDef_of_quadratic_le {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.IsHermitian)
    (hAB:∀ x,x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ (B *ᵥ x)):B.PosDef:=by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB
  intro x hx
  have hpos:0 < x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.dotProduct_mulVec_pos hx
  simpa using hpos.trans_le (hAB x)

theorem inverse_variational_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (x y:ι→ ℝ):
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:A *ᵥ (A⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hnonneg:0≤ (y - A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (y - A⁻¹ *ᵥ x)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (y - A⁻¹ *ᵥ x)
  rw [Matrix.mulVec_sub,hcancel,sub_dotProduct,dotProduct_sub,
    dotProduct_sub,symmetric_form hA.1 (A⁻¹ *ᵥ x) y,hcancel,
    dotProduct_comm y x,dotProduct_comm (A⁻¹ *ᵥ x) x] at hnonneg
  linarith

theorem inverse_quadratic_antitone {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef)
    (hAB:∀ y,y ⬝ᵥ (A *ᵥ y)≤ y ⬝ᵥ (B *ᵥ y)) (x:ι→ ℝ):
    x ⬝ᵥ (B⁻¹ *ᵥ x)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:B *ᵥ (B⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit),Matrix.one_mulVec]
  have hvar:=inverse_variational_bound hA x (B⁻¹ *ᵥ x)
  have hle:=hAB (B⁻¹ *ᵥ x)
  rw [hcancel,dotProduct_comm (B⁻¹ *ᵥ x) x] at hle
  linarith

def realShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ):
    Matrix (Fin n) (Fin n) ℝ:=fun i j => (A i j:ℝ)

theorem enlargement_sandwich {n:ℕ} (A R:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (herr:∀ i j, |R i j - A i j|≤ ε)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)∧
      x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)≤
        x ⬝ᵥ (A *ᵥ x) + 2 * (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have h:=quadratic_error_bound (R - A) ε hε herr x
  rw [Matrix.sub_mulVec,dotProduct_sub] at h
  have hh:=abs_le.mp h
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  constructor <;> linarith [hh.1,hh.2]

theorem roundedShape_sandwich {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape A *ᵥ x)≤ x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)∧
      x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
        x ⬝ᵥ (realShape A *ᵥ x) + (2 * (n:ℝ) / D) * (x ⬝ᵥ x):=by
  let R:Matrix (Fin n) (Fin n) ℝ:=
    fun i j => (RationalRounding.roundDown (A i j) D:ℝ)
  have herr:∀ i j, |R i j - realShape A i j|≤ 1 / (D:ℝ):=by
    intro i j
    have h:=RationalRounding.roundDown_error (A i j) D hD
    dsimp [R,realShape]
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]
  have hid:realShape (roundedShape A D)=R + ((n:ℝ) * (1 / D)) • 1:=by
    ext i j
    change ((RationalRounding.roundDown (A i j) D +
      ((n:ℚ) / D) * (if i=j then 1 else 0):ℚ):ℝ) =
      (RationalRounding.roundDown (A i j) D:ℝ) +
        ((n:ℝ) * (1 / D)) * (if i=j then 1 else 0)
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hid]
  simpa only [mul_one_div] using
    enlargement_sandwich (realShape A) R (1 / D) (by positivity) herr x

theorem roundedShape_isHermitian {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:A.IsSymm) (D:ℕ):(realShape (roundedShape A D)).IsHermitian:=by
  rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
  intro i j
  simp [realShape,roundedShape,hA.apply i j,Matrix.one_apply,eq_comm]

theorem roundedShape_posDef {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape A D)).PosDef:=by
  have hsym:A.IsSymm:=by
    apply Matrix.IsSymm.ext
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    dsimp [realShape] at h
    exact_mod_cast h
  exact posDef_of_quadratic_le hA (roundedShape_isHermitian A hsym D)
    (fun x => (roundedShape_sandwich A D hD x).1)

theorem roundedShape_contains {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ)
    (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1):
    x ⬝ᵥ ((realShape (roundedShape A D))⁻¹ *ᵥ x)≤ 1:=
  (inverse_quadratic_antitone hA (roundedShape_posDef A hA D hD)
    (fun y => (roundedShape_sandwich A D hD y).1) x).trans hx

theorem roundedShape_relative_bound {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (lowerBound η:ℝ) (hη:0≤ η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ η * lowerBound) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
      (1 + η) * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  have hxx:0≤ x ⬝ᵥ x:=by
    simpa using dotProduct_star_self_nonneg x
  have herror:=mul_le_mul_of_nonneg_right hprecision hxx
  have hrelative:=mul_le_mul_of_nonneg_left (hlower x) hη
  have hround:=(roundedShape_sandwich A D hD x).2
  nlinarith only [herror,hrelative,hround]

theorem inverse_smul {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (k:ℝ) (hk:k ≠ 0):
    (k • A)⁻¹=k⁻¹ • A⁻¹:=by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    inv_mul_cancel₀ hk,one_smul]

theorem inverse_form_upper_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x)) (x:ι→ ℝ):
    x ⬝ᵥ (A⁻¹ *ᵥ x)≤ lowerBound⁻¹ * (x ⬝ᵥ x):=by
  have hI:(1:Matrix ι ι ℝ).PosDef:=Matrix.PosDef.one
  have hlI:(lowerBound • (1:Matrix ι ι ℝ)).PosDef:=hI.smul hl
  have horder:∀ y,y ⬝ᵥ ((lowerBound • (1:Matrix ι ι ℝ)) *ᵥ y)≤
      y ⬝ᵥ (A *ᵥ y):=by
    intro y
    simpa only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
      smul_eq_mul] using hbound y
  have h:=inverse_quadratic_antitone hlI hA horder x
  rw [inverse_smul hI lowerBound (ne_of_gt hl)] at h
  simpa only [inv_one,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul] using h

theorem center_displacement_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ (A *ᵥ (x + e))≤ (1 + η) ^ 2:=by
  have hnonneg:0≤ (η • x - e) ⬝ᵥ (A *ᵥ (η • x - e)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (η • x - e)
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    symmetric_form hA.1 e x] at hnonneg
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hA.1 e x]
  have hb₁:=mul_le_mul_of_nonneg_left hx (show 0≤ η ^ 2 + η by positivity)
  have hb₂:=mul_le_mul_of_nonneg_left he (show 0≤ 1 + η by positivity)
  nlinarith only [hnonneg,hb₁,hb₂,hη]

theorem enlargedShape_contains_displaced {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ ((((1 + η) ^ 2) • A)⁻¹ *ᵥ (x + e))≤ 1:=by
  have hk:0 < (1 + η) ^ 2:=by positivity
  rw [inverse_smul hA _ (ne_of_gt hk),Matrix.smul_mulVec,
    dotProduct_smul,smul_eq_mul]
  calc
    _≤ ((1 + η) ^ 2)⁻¹ * (1 + η) ^ 2:=
      mul_le_mul_of_nonneg_left (center_displacement_bound hA.inv η hη x e hx he)
        (inv_nonneg.mpr (le_of_lt hk))
    _=1:=inv_mul_cancel₀ (ne_of_gt hk)

theorem roundedCenter_error {n:ℕ} {A:Matrix (Fin n) (Fin n) ℝ}
    (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x))
    (c:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    let e:Fin n→ ℝ:=fun i => (c i:ℝ) - RationalRounding.roundDown (c i) D
    e ⬝ᵥ (A⁻¹ *ᵥ e)≤ lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2):=by
  dsimp only
  apply (inverse_form_upper_bound hA lowerBound hl hbound _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hl))
  simpa only [dotProduct, ← pow_two] using
    RationalRounding.roundDown_vector_error n c D hD

end Lax109476Proofs.EllipsoidRounding

end

section

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

theorem form_cauchy_schwarz {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (a x:ι→ ℝ) (ha:a ≠ 0):
    (x ⬝ᵥ (A *ᵥ a)) ^ 2≤ (a ⬝ᵥ (A *ᵥ a)) * (x ⬝ᵥ (A *ᵥ x)):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnonneg:0≤ (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (q • x - t • a)
  have hid:(q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) =
      q * (q * (x ⬝ᵥ (A *ᵥ x)) - t ^ 2):=by
    simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
      dotProduct_sub,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.1 a x]
    dsimp [q,t]
    ring
  rw [hid] at hnonneg
  have h:=nonneg_of_mul_nonneg_right hnonneg hq
  change t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x))
  linarith

noncomputable def realCutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ)
    (a:Fin n→ ℝ):Matrix (Fin n) (Fin n) ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) •
    (A - (2 / (((n:ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

theorem realShape_cutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    realShape (cutShape n A a)=realCutShape n (realShape A) (fun i => (a i:ℝ)):=by
  ext i j
  simp [realShape,cutShape,realCutShape,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct,Rat.cast_sum,smul_eq_mul]

theorem realCutShape_sandwich (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2 * (x ⬝ᵥ (A *ᵥ x))≤
      x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
    x ⬝ᵥ (realCutShape n A a *ᵥ x)≤
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hα:0 < α:=by dsimp [α]; apply div_pos <;> nlinarith
  have hβ:0≤ β:=by dsimp [β]; positivity
  have hcs:t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x)):=form_cauchy_schwarz hA a x ha
  have hcs':t ^ 2 / q≤ x ⬝ᵥ (A *ᵥ x):=(div_le_iff₀ hq).mpr (by nlinarith)
  have hterm:0≤ β * (t ^ 2 / q):=by positivity
  have htermUpper:=mul_le_mul_of_nonneg_left hcs' hβ
  have hid:x ⬝ᵥ (realCutShape n A a *ᵥ x) =
      α * ((x ⬝ᵥ (A *ᵥ x)) - β * (t ^ 2 / q)):=by
    simp only [realCutShape,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.vecMulVec_mulVec,dotProduct_smul,dotProduct_sub,
      smul_eq_mul]
    dsimp [α,β,q,t]
    simp only [dotProduct_comm (A *ᵥ a) x,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hfactor:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  rw [hid, ← hfactor]
  constructor
  · have h:=mul_le_mul_of_nonneg_left htermUpper (le_of_lt hα)
    nlinarith only [h]
  · have h:=mul_nonneg (le_of_lt hα) hterm
    nlinarith only [h]

theorem realCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):(realCutShape n A a).PosDef:=by
  have hsym:(realCutShape n A a).IsHermitian:=by
    rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    simp [realCutShape,Matrix.smul_apply,Matrix.sub_apply,Matrix.vecMulVec,
      smul_eq_mul,h,mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by positivity
  have hxx:0 < x ⬝ᵥ (A *ᵥ x):=by simpa using hA.dotProduct_mulVec_pos hx
  simpa using (mul_pos hp hxx).trans_le (realCutShape_sandwich n hn A hA a x ha).1

theorem realCutShape_inverse (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a)⁻¹ =
      (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) •
        (A⁻¹ + (2 / (((n:ℝ) - 1) * (a ⬝ᵥ (A *ᵥ a)))) •
          Matrix.vecMulVec a a):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnzero:(n:ℝ) ≠ 0:=by linarith
  have hminus:(n:ℝ) - 1 ≠ 0:=by linarith
  have hplus:(n:ℝ) + 1 ≠ 0:=by linarith
  have hdiff:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hAA:A * A⁻¹=1:=Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hrow:(A *ᵥ a) ᵥ* A⁻¹=a:=by
    rw [Matrix.vecMul_mulVec, (Matrix.isHermitian_iff_isSymm.mp hA.1).eq,
      hAA,Matrix.vecMul_one]
  have hcross:Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) * Matrix.vecMulVec a a =
      (a ⬝ᵥ (A *ᵥ a)) • Matrix.vecMulVec (A *ᵥ a) a:=by
    rw [Matrix.vecMulVec_mul_vecMulVec,dotProduct_comm]
    ext i j
    simp [Matrix.vecMulVec,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm]
  apply Matrix.inv_eq_right_inv
  unfold realCutShape
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hc:(((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1))=1:=by field_simp
  rw [hc,one_smul]
  simp only [mul_add,sub_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [hAA,hcross,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hrow]
  simp only [smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ring

theorem det_realCutShape (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a).det=A.det * EllipsoidStep.determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:q ≠ 0:=by
    have hp:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hfactor:A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) =
      A * (1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)):=by
    rw [mul_sub,Matrix.mul_one,Matrix.mul_smul,Matrix.mul_vecMulVec]
  have hdet:(1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)).det=1 - β:=by
    have h:=Matrix.det_one_add_replicateCol_mul_replicateRow
      (ι:=Unit) a (-(β / q) • (A *ᵥ a))
    have hd:a ⬝ᵥ (-(β / q) • (A *ᵥ a))=-β:=by
      rw [dotProduct_smul]
      change -(β / q) * q=-β
      field_simp
    have hd':(-(β / q) • (A *ᵥ a)) ⬝ᵥ a=-β:=by
      rw [dotProduct_comm]
      exact hd
    rw [hd'] at h
    simpa [← Matrix.vecMulVec_eq Unit,sub_eq_add_neg,neg_smul] using h
  have hform:realCutShape n A a =
      α • (A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a)):=by
    dsimp [realCutShape,α,β,q]
    congr 2
    congr 1
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [hform,Matrix.det_smul,Fintype.card_fin,hfactor,Matrix.det_mul,hdet]
  have hαβ:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  unfold EllipsoidStep.determinantFactor
  calc
    _=A.det * (α ^ (n - 1) * (α * (1 - β))):=by
      nth_rewrite 1 [show n=(n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    _=_:=by rw [hαβ]

theorem realCutShape_quadratic (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) =
      EllipsoidStep.centralCutForm n (x ⬝ᵥ (A⁻¹ *ᵥ x))
        ((a ⬝ᵥ x) / Real.sqrt q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let s:=1 / (((n:ℝ) + 1) * Real.sqrt q)
  let z:=x + s • (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hzz:z ⬝ᵥ (A⁻¹ *ᵥ z) =
      x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q:=by
    dsimp [z]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,hc,add_dotProduct,
      dotProduct_add,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.inv.1 (A *ᵥ a) x,dotProduct_comm x a,
      dotProduct_comm (A *ᵥ a) a]
    dsimp [q]
    ring
  have haz:a ⬝ᵥ z=a ⬝ᵥ x + s * q:=by
    simp [z,q,dotProduct_add,dotProduct_smul]
  change z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)=_
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    dotProduct_smul,dotProduct_add,smul_eq_mul,dotProduct_comm z a]
  rw [hzz,haz]
  simp only [op_smul_eq_smul,smul_eq_mul]
  change (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
    ((x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q) +
      (2 / (((n:ℝ) - 1) * q)) * (((a ⬝ᵥ x) + s * q) * ((a ⬝ᵥ x) + s * q)))=_
  dsimp [s,EllipsoidStep.centralCutForm]
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  rw [← htsq]
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem realCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1) (hcut:a ⬝ᵥ x≤ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)≤ 1:=by
  dsimp only
  rw [realCutShape_quadratic n hn A hA a x ha]
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hav:A *ᵥ a ≠ 0:=by
    intro h
    have h':=hc
    rw [h,Matrix.mulVec_zero] at h'
    exact ha h'.symm
  have hcs:=form_cauchy_schwarz hA.inv (A *ᵥ a) x hav
  rw [hc,dotProduct_comm x a,dotProduct_comm (A *ᵥ a) a] at hcs
  have hcs':((a ⬝ᵥ x) / Real.sqrt q) ^ 2≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
    rw [div_pow,Real.sq_sqrt (le_of_lt hq)]
    apply (div_le_iff₀ hq).mpr
    simpa [q,mul_comm] using hcs
  have ht:-1≤ (a ⬝ᵥ x) / Real.sqrt q:=by nlinarith
  exact EllipsoidStep.centralCutForm_le_one n _ _ (by exact_mod_cast hn)
    hx ht (div_nonpos_of_nonpos_of_nonneg hcut (le_of_lt hs))

theorem roundedCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape (cutShape n A a) D)).PosDef:=by
  apply roundedShape_posDef _ _ D hD
  rw [realShape_cutShape]
  exact realCutShape_posDef n hn (realShape A) hA _ ha

theorem roundedCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D)
    (x:Fin n→ ℝ) (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1)
    (hcut:(fun i => (a i:ℝ)) ⬝ᵥ x≤ 0):
    let ar:Fin n→ ℝ:=fun i => (a i:ℝ)
    let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (realShape A *ᵥ ar)
    z ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ z)≤ 1:=by
  have hQ:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA _ ha
  apply roundedShape_contains _ hQ D hD
  rw [realShape_cutShape]
  exact realCutShape_contains n hn (realShape A) hA _ x ha hx hcut

theorem realCutShape_coarse_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    (1 / 4:ℝ) * (x ⬝ᵥ (A *ᵥ x))≤ x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
      x ⬝ᵥ (realCutShape n A a *ᵥ x)≤ 2 * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hxx:0≤ x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hp:0 < (n:ℝ) + 1:=by linarith
  have hd:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  have hratio:(1 / 2:ℝ)≤ (n:ℝ) / ((n:ℝ) + 1):=
    (le_div_iff₀ hp).mpr (by linarith)
  have hlo:(1 / 4:ℝ)≤ ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    nlinarith
  have hhi:(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)≤ 2:=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have h:=realCutShape_sandwich n hn A hA a x ha
  exact ⟨(mul_le_mul_of_nonneg_right hlo hxx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hhi hxx)⟩

theorem dyadic_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (2:ℝ) ^ (l + s + n + 1)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hpow:(0:ℝ) < 2 ^ (l + s + n + 1):=by positivity
  apply (div_le_iff₀ hpow).mpr
  simp only [pow_add,pow_one]
  have hl:(2:ℝ) ^ l ≠ 0:=by positivity
  have hs:(2:ℝ) ^ s ≠ 0:=by positivity
  field_simp
  nlinarith

end Lax109476Proofs.EllipsoidBounds

end

section

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

theorem cut_direction_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (A *ᵥ a) ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ (A *ᵥ a)) =
      (((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * (a ⬝ᵥ (A *ᵥ a)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    hc,dotProduct_smul,dotProduct_add,smul_eq_mul,
    op_smul_eq_smul,dotProduct_comm (A *ᵥ a) a]
  field_simp
  ring

theorem center_approximation_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r:ℝ) (hr:0 < r):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e) =
      ((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2:=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hrz:r ≠ 0:=ne_of_gt hr
  dsimp only
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [cut_direction_form n hn A hA a ha]
  change _=((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  change (1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
    ((1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
      ((((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * q))=_
  rw [← htsq]
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem center_approximation_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r ε:ℝ)
    (hr:Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ r)
    (herr:r - Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ ε):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e)≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hrp:0 < r:=hs.trans_le hr
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have ht:0≤ r - Real.sqrt q:=by linarith
  have hε:0≤ ε:=ht.trans herr
  have hsquare:q≤ r ^ 2:=by nlinarith [Real.sq_sqrt (le_of_lt hq)]
  dsimp only
  rw [center_approximation_form n hn A hA a ha r hrp,div_pow,mul_pow]
  change (r - Real.sqrt q) ^ 2 / ((n:ℝ) ^ 2 * r ^ 2)≤ _
  calc
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * r ^ 2):=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=
      div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))

theorem form_add_le_two {ι:Type} [Fintype ι] [DecidableEq ι]
    {B:Matrix ι ι ℝ} (hB:B.PosDef) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (B *ᵥ (u + v))≤
      2 * (u ⬝ᵥ (B *ᵥ u)) + 2 * (v ⬝ᵥ (B *ᵥ v)):=by
  have h:0≤ (u - v) ⬝ᵥ (B *ᵥ (u - v)):=by
    simpa using hB.posSemidef.dotProduct_mulVec_nonneg (u - v)
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,
    symmetric_form hB.1 v u] at h
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hB.1 v u]
  linarith

noncomputable def exactCenter (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ):Fin n→ ℝ:=
  realVector c -
    (1 / (((n:ℝ) + 1) * Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
      (realShape A *ᵥ realVector a)

theorem cast_direction_form (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ)=realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
  simp [dotProduct,Matrix.mulVec,realShape,realVector,Rat.cast_sum]

theorem approximateCenter_difference (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    exactCenter n A a c - realVector (approximateCenter n A a c D) =
      (1 / (((n:ℝ) + 1) * (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ)) -
        1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
        (realShape A *ᵥ realVector a):=by
  ext i
  simp [exactCenter,approximateCenter,realVector,realShape,Matrix.mulVec,
    dotProduct,Rat.cast_sum,smul_eq_mul]
  ring

theorem roundedCenter_total_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound η:ℝ) (hl:0 < lowerBound)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ η ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ η ^ 2 / 4):
    let e:=exactCenter n A a c - realVector (roundedCenter n A a c D)
    e ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ e)≤ η ^ 2:=by
  let ar:=realVector a
  let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
  let Q:=realShape (roundedShape (cutShape n A a) D)
  let e₁:=exactCenter n A a c - realVector (approximateCenter n A a c D)
  let e₂:=realVector (approximateCenter n A a c D) - realVector (roundedCenter n A a c D)
  have hq:0 < q:=by simpa [q,ar] using hA.dotProduct_mulVec_pos ha
  have hqrat:0≤ a ⬝ᵥ (A *ᵥ a):=by
    have hp:(0:ℝ)≤ ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ):=by
      rw [cast_direction_form]
      exact le_of_lt hq
    exact_mod_cast hp
  have hQ:Q.PosDef:=roundedCutShape_posDef n hn A hA a ha D hD
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA ar ha
  have horder:∀ y,y ⬝ᵥ (realShape (cutShape n A a) *ᵥ y)≤ y ⬝ᵥ (Q *ᵥ y):=
    fun y => (roundedShape_sandwich (cutShape n A a) D hD y).1
  have h₁:e₁ ⬝ᵥ (Q⁻¹ *ᵥ e₁)≤ η ^ 2 / 4:=by
    apply (inverse_quadratic_antitone hC hQ horder e₁).trans
    rw [realShape_cutShape]
    obtain ⟨hr,herr⟩:=RationalRounding.sqrtUpper_bounds (a ⬝ᵥ (A *ᵥ a)) hqrat D hD
    rw [cast_direction_form] at hr herr
    have hb:=center_approximation_error n hn (realShape A) hA ar ha
      (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ) (2 / D) hr (by linarith)
    change e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤ _
    have hid:(2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q) =
        4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 * q):=by ring
    have hb':e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤
        (2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q):=by
      dsimp [e₁]
      rw [approximateCenter_difference]
      exact hb
    exact hb'.trans (hid ▸ hsqrt)
  have h₂:e₂ ⬝ᵥ (Q⁻¹ *ᵥ e₂)≤ η ^ 2 / 4:=by
    have h:=roundedCenter_error hQ lowerBound hl hlower (approximateCenter n A a c D) D hD
    exact h.trans hgrid
  have he:exactCenter n A a c - realVector (roundedCenter n A a c D)=e₁ + e₂:=by
    dsimp [e₁,e₂]
    abel
  dsimp only
  rw [he]
  have h:=form_add_le_two hQ.inv e₁ e₂
  linarith

theorem realShape_roundedStepShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (η:ℚ):
    realShape (roundedStepShape n A a D η) =
      ((1 + (η:ℝ)) ^ 2) • realShape (roundedShape (cutShape n A a) D):=by
  ext i j
  simp [realShape,roundedStepShape,Matrix.smul_apply,smul_eq_mul]

theorem roundedStepShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η):(realShape (roundedStepShape n A a D η)).PosDef:=by
  rw [realShape_roundedStepShape]
  apply (roundedCutShape_posDef n hn A hA a ha D hD).smul
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  positivity

theorem roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound:ℝ) (hl:0 < lowerBound) (η:ℚ) (hη:0 < η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ (η:ℝ) ^ 2 / 4)
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  have hQ:=roundedCutShape_posDef n hn A hA a ha D hD
  have he:=roundedCenter_total_error n hn A hA a c ha D hD lowerBound η hl hlower hsqrt hgrid
  have hxe:(x - exactCenter n A a c) ⬝ᵥ
      ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ
        (x - exactCenter n A a c))≤ 1:=by
    have h:=roundedCutShape_contains n hn A hA a ha D hD (x - realVector c) hx hcut
    have hid:x - exactCenter n A a c=x - realVector c +
        (1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
            (realShape A *ᵥ realVector a):=by
      unfold exactCenter
      abel
    rw [hid]
    exact h
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have h:=enlargedShape_contains_displaced hQ η hp
    (x - exactCenter n A a c)
    (exactCenter n A a c - realVector (roundedCenter n A a c D)) hxe he
  rw [realShape_roundedStepShape]
  simpa only [sub_add_sub_cancel] using h

end Lax109476Proofs.EllipsoidCenter

end

section

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

theorem gridDenominator_pos (l s n:ℕ):0 < gridDenominator l s n:=by
  unfold gridDenominator
  positivity

theorem gridDenominator_size (l s n:ℕ):
    Nat.size (gridDenominator l s n)=l + s + n + 4:=by
  unfold gridDenominator
  rw [Nat.size_pow]

theorem grid_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (gridDenominator l s n:ℝ)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hp:(2:ℝ) ^ (l + s + n + 1)≤ (gridDenominator l s n:ℝ):=by
    unfold gridDenominator
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show l + s + n + 1≤ l + s + n + 3 by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (dyadic_shape_precision l s n)

theorem dyadic_center_precision (l s n:ℕ):
    4 / (((gridDenominator l s n:ℕ):ℝ) ^ 2 * ((2:ℝ) ^ l)⁻¹)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4∧
    (((2:ℝ) ^ l)⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4:=by
  let L:=(2:ℝ) ^ l
  let S:=(2:ℝ) ^ s
  let N:=(2:ℝ) ^ (n + 3)
  have hL:1≤ L:=one_le_pow₀ (by norm_num)
  have hS:0 < S:=by dsimp [S]; positivity
  have hN:8≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    have h:=one_le_pow₀ (show (1:ℝ)≤ 2 by norm_num) (n:=n)
    linarith
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hnN:8 * (n:ℝ)≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    nlinarith
  have hLN:N ^ 2≤ L * N ^ 2:=by
    simpa using mul_le_mul_of_nonneg_right hL (sq_nonneg N)
  have hid:(gridDenominator l s n:ℝ)=L * S * N:=by
    simp only [gridDenominator,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [L,S,N]
    rw [show l + s + n + 3=l + s + (n + 3) by omega,pow_add,pow_add]
  have hLz:L ≠ 0:=by linarith
  have hSz:S ≠ 0:=ne_of_gt hS
  have hNz:N ≠ 0:=by linarith
  change 4 / ((gridDenominator l s n:ℝ) ^ 2 * L⁻¹)≤ (S⁻¹) ^ 2 / 4∧
    (L⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤ (S⁻¹) ^ 2 / 4
  rw [hid,inv_inv]
  constructor
  · field_simp
    nlinarith only [hN,hLN]
  · field_simp
    nlinarith only [hN,hnN,hLN]

theorem exactCut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
  have he:((2:ℝ) ^ (l + 2))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
    rw [pow_add]
    norm_num
  rw [he]
  calc
    _=(1 / 4:ℝ) * (((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)):=by ring
    _≤ (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)):=
      mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
    _≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      rw [realShape_cutShape]
      exact (realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha).1

theorem cut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=
  (exactCut_lower_bound n hn A hA a ha l hbound x).trans
    (roundedShape_sandwich (cutShape n A a) D hD x).1

theorem uniform_roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l s:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    let D:=gridDenominator (l + 2) s n
    let η:ℚ:=1 / (2:ℚ) ^ s
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  let D:=gridDenominator (l + 2) s n
  let η:ℚ:=1 / (2:ℚ) ^ s
  let lowerBound:=((2:ℝ) ^ (l + 2))⁻¹
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hη:0 < η:=by dsimp [η]; positivity
  have hl:0 < lowerBound:=by dsimp [lowerBound]; positivity
  have hcast:(η:ℝ)=((2:ℝ) ^ s)⁻¹:=by simp [η]
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hlower:=cut_lower_bound n hn A hA a ha D hD l hbound
  have hq:lowerBound≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
    have he:lowerBound=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
      dsimp [lowerBound]
      rw [pow_add]
      norm_num
    have hp:0≤ ((2:ℝ) ^ l)⁻¹:=by positivity
    have h:=hbound (realVector a)
    have h':=mul_le_mul_of_nonneg_left hanorm hp
    rw [he]
    nlinarith only [h,h',hp]
  have hprec:=dyadic_center_precision (l + 2) s n
  have hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4:=by
    rw [hcast]
    apply le_trans _ hprec.1
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    have hn₂:1≤ (n:ℝ) ^ 2:=by nlinarith
    have hprod:=mul_le_mul_of_nonneg_left hq (sq_nonneg (D:ℝ))
    have hqp:0≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by linarith
    have h:=mul_le_mul_of_nonneg_right hn₂
      (mul_nonneg (sq_nonneg (D:ℝ)) hqp)
    nlinarith only [hprod,h]
  apply roundedStep_contains n hn A hA a c ha D hD lowerBound hl η hη hlower hsqrt
  · simpa only [hcast] using hprec.2
  · exact hx
  · exact hcut

end Lax109476Proofs.EllipsoidPrecision

end

section

namespace Lax109476Proofs.EllipsoidDeterminant

open Matrix EllipsoidRounding

theorem eigenvalue_le_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)) (i:ι):
    hA.eigenvalues i≤ k:=by
  let v:ι→ ℝ:=(hA.eigenvectorBasis i).ofLp
  have hv:v ≠ 0:=by
    intro h
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun h j
  have hxx:0 < v ⬝ᵥ v:=by
    simpa using (dotProduct_star_self_pos_iff (v:=v)).mpr hv
  have he:A *ᵥ v=hA.eigenvalues i • v:=hA.mulVec_eigenvectorBasis i
  have h:=hbound v
  rw [he,dotProduct_smul,smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hxx).mp h

theorem det_le_pow_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosSemidef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)):
    A.det≤ k ^ Fintype.card ι:=by
  rw [hA.1.det_eq_prod_eigenvalues]
  simpa [RCLike.ofReal_real_eq_id] using Finset.prod_le_prod
    (s:=Finset.univ (α:=ι)) (g:=fun _ => k)
    (fun i _ => hA.eigenvalues_nonneg i)
    (fun i _ => eigenvalue_le_of_form_bound hA.1 k hbound i)

theorem det_le_relative_pow {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (B *ᵥ x)≤ k * (x ⬝ᵥ (A *ᵥ x))):
    B.det≤ k ^ Fintype.card ι * A.det:=by
  open scoped MatrixOrder in
  have hsqrt:∃ R:Matrix ι ι ℝ,R.IsHermitian∧ IsUnit R∧ R * R=A:=by
    let R:=CFC.sqrt A
    have hRR:R * R=A:=by
      simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
    have hu:IsUnit (R * R):=hRR.symm ▸ hA.isUnit
    exact ⟨R, (CFC.sqrt_nonneg A).posSemidef.1,
      isUnit_of_mul_isUnit_left hu,hRR⟩
  obtain ⟨R,hR,hu,hRR⟩:=hsqrt
  have hRinv:R⁻¹.IsHermitian:=hR.inv
  have hRi:IsUnit R⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hu
  have hRRi:R * R⁻¹=1:=Matrix.mul_nonsing_inv R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRiR:R⁻¹ * R=1:=Matrix.nonsing_inv_mul R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  let C:=R⁻¹ * B * R⁻¹
  have hC:C.PosDef:=by
    simpa only [hRinv.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hRi)
  have hid:R⁻¹ * A * R⁻¹=1:=by
    rw [← hRR, ← Matrix.mul_assoc,hRiR,Matrix.one_mul,hRRi]
  have hform (M:Matrix ι ι ℝ) (x:ι→ ℝ):
      x ⬝ᵥ ((R⁻¹ * M * R⁻¹) *ᵥ x) =
        (R⁻¹ *ᵥ x) ⬝ᵥ (M *ᵥ (R⁻¹ *ᵥ x)):=by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact (symmetric_form hRinv x (M *ᵥ (R⁻¹ *ᵥ x))).trans (dotProduct_comm _ _)
  have hb:∀ x,x ⬝ᵥ (C *ᵥ x)≤ k * (x ⬝ᵥ x):=by
    intro x
    have h:=hbound (R⁻¹ *ᵥ x)
    rw [← hform B x, ← hform A x,hid,Matrix.one_mulVec] at h
    exact h
  have hc:=det_le_pow_of_form_bound hC.posSemidef k hb
  have hdet:B.det=C.det * A.det:=by
    dsimp [C]
    rw [Matrix.det_mul,Matrix.det_mul, ← hRR,Matrix.det_mul]
    have hd:R.det * (R⁻¹).det=1:=by
      rw [← Matrix.det_mul,hRRi,Matrix.det_one]
    calc
      _=B.det * (R.det * (R⁻¹).det) ^ 2:=by rw [hd]; ring
      _=_:=by ring
  rw [hdet]
  exact mul_le_mul_of_nonneg_right hc (le_of_lt hA.det_pos)

end Lax109476Proofs.EllipsoidDeterminant

end

section

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant Lax109476.RationalCertificates

theorem stepAccuracy_pos (n:ℕ):0 < stepAccuracy n:=by
  unfold stepAccuracy
  positivity

theorem stepAccuracy_small (n:ℕ) (hn:2≤ n):
    (stepAccuracy n:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < 8 * (n:ℝ) * ((n:ℝ) + 1):=by positivity
  have h₁:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have h₂:(n:ℝ) + 1≤ (2:ℝ) ^ (n + 1):=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n + 1)).le
  have hprod:=mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have he:(2:ℝ) ^ (2 * n + 4)=8 * ((2:ℝ) ^ n * (2:ℝ) ^ (n + 1)):=by
    rw [← pow_add,show 2 * n + 4=(n + (n + 1)) + 3 by omega,pow_add]
    norm_num
    ring
  have hb:8 * (n:ℝ) * ((n:ℝ) + 1)≤ (2:ℝ) ^ (2 * n + 4):=by
    rw [he]
    nlinarith only [hprod]
  simp only [stepAccuracy,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hp hb

theorem storedShape_relative_bound (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (hD:0 < D) (η:ℚ) (hη:0≤ η)
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + (η:ℝ)) ^ 3 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
  have hp:(0:ℝ)≤ η:=by exact_mod_cast hη
  have h:=roundedShape_relative_bound (cutShape n A a) D hD lowerBound η hp hlower hprecision x
  rw [realShape_roundedStepShape]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  calc
    _≤ (1 + (η:ℝ)) ^ 2 *
        ((1 + (η:ℝ)) * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))):=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _=_:=by ring

theorem storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η)
    (hsmall:(η:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)))
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound):
    Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have hη₁:(η:ℝ)≤ 1:=by
    have hh:1 / (8 * (n:ℝ) * ((n:ℝ) + 1))≤ 1:=
      (div_le_one (by positivity)).mpr (by nlinarith)
    exact hsmall.trans hh
  have hscalar:(1 + (η:ℝ)) ^ 3≤ (1 + 2 * (η:ℝ)) ^ 2:=by
    have hsq:(η:ℝ) ^ 2≤ η:=by nlinarith
    have hcube:=mul_le_mul_of_nonneg_left hsq (le_of_lt hp)
    nlinarith only [hcube,hp,sq_nonneg (η:ℝ)]
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hP:=roundedStepShape_posDef n hn A hA a ha D hD η hη
  have hrelative:∀ x,x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + 2 * (η:ℝ)) ^ 2 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
    intro x
    have hnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
    exact (storedShape_relative_bound n A a D hD η (le_of_lt hη) lowerBound hlower hprecision x).trans
      (mul_le_mul_of_nonneg_right hscalar hnonneg)
  have hdet:=det_le_relative_pow hC hP ((1 + 2 * (η:ℝ)) ^ 2) hrelative
  rw [Fintype.card_fin] at hdet
  have hpow:((1 + 2 * (η:ℝ)) ^ 2) ^ n=((1 + 2 * (η:ℝ)) ^ n) ^ 2:=by
    rw [← pow_mul, ← pow_mul,Nat.mul_comm]
  have hsqrt:Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realShape (cutShape n A a)).det:=by
    have h:=Real.sqrt_le_sqrt hdet
    rw [hpow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)] at h
    exact h
  have hδ:2 * (η:ℝ)≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1)):=by
    calc
      _≤ 2 * (1 / (8 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _=_:=by
        simp only [div_eq_mul_inv,_root_.mul_inv_rev]
        norm_num
        ring
  have hshrink:=EllipsoidStep.enlarged_shrink_bound n hn (2 * (η:ℝ))
    (by positivity) hδ
  rw [realShape_cutShape] at hsqrt
  change Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
    (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realCutShape n (realShape A) (realVector a)).det at hsqrt
  rw [det_realCutShape n hn (realShape A) hA (realVector a) ha] at hsqrt
  rw [Real.sqrt_mul (le_of_lt hA.det_pos)] at hsqrt
  calc
    _≤ ((1 + 2 * (η:ℝ)) ^ n * Real.sqrt (EllipsoidStep.determinantFactor n)) *
        Real.sqrt (realShape A).det:=by nlinarith only [hsqrt]
    _≤ _:=mul_le_mul_of_nonneg_right hshrink (Real.sqrt_nonneg _)

theorem uniform_storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)):
    Real.sqrt (realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hprec:=grid_shape_precision (l + 2) (2 * n + 4) n
  have hcast:(stepAccuracy n:ℝ)=((2:ℝ) ^ (2 * n + 4))⁻¹:=by
    simp [stepAccuracy]
  apply storedStep_shrink n hn A hA a ha _ (gridDenominator_pos _ _ _)
    (stepAccuracy n) (stepAccuracy_pos n) (stepAccuracy_small n hn)
    (((2:ℝ) ^ (l + 2))⁻¹) (exactCut_lower_bound n hn A hA a ha l hbound)
  simpa only [hcast] using hprec

theorem uniform_storedStep_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)) (x:Fin n→ ℝ):
    let P:=realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))
    (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤ x ⬝ᵥ (P *ᵥ x)∧
      x ⬝ᵥ (P *ᵥ x)≤ 4 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  let D:=gridDenominator (l + 2) (2 * n + 4) n
  let η:=stepAccuracy n
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hp:(0:ℝ) < η:=by exact_mod_cast stepAccuracy_pos n
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hη:(η:ℝ)≤ 1 / 8:=by
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    apply (stepAccuracy_small n hn).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hR:=roundedCutShape_posDef n hn A hA a ha D hD
  have hnonneg:0≤ x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hcutnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor:1≤ (1 + (η:ℝ)) ^ 2:=by nlinarith
  have hfactorUpper:(1 + (η:ℝ)) ^ 3≤ 2:=by
    calc
      _≤ (9 / 8:ℝ) ^ 3:=pow_le_pow_left₀ (by positivity) (by linarith) 3
      _≤ _:=by norm_num
  have hprec:2 * (n:ℝ) / D≤ (η:ℝ) * ((2:ℝ) ^ (l + 2))⁻¹:=by
    simpa [η,stepAccuracy] using grid_shape_precision (l + 2) (2 * n + 4) n
  have hrelative:=storedShape_relative_bound n A a D hD η (le_of_lt (stepAccuracy_pos n))
    _ (exactCut_lower_bound n hn A hA a ha l hbound) hprec x
  have hcoarse:=realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha
  have hcoarse':(1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)∧
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)≤ 2 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
    rw [realShape_cutShape]
    exact hcoarse
  dsimp only
  constructor
  · apply hcoarse'.1.trans
    apply (roundedShape_sandwich (cutShape n A a) D hD x).1.trans
    rw [realShape_roundedStepShape]
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact le_mul_of_one_le_left hnonneg hfactor
  · apply hrelative.trans
    have h:=mul_le_mul_of_nonneg_right hfactorUpper hcutnonneg
    nlinarith only [h,hcoarse'.2]

end Lax109476Proofs.EllipsoidIteration

end

section

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

def shapes (n:ℕ) (a:ℕ→ Fin n→ ℚ):ℕ→ Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

def centers (n:ℕ) (a:ℕ→ Fin n→ ℚ) (c₀:Fin n→ ℚ):ℕ→ Fin n→ ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

theorem shapes_invariant (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    (realShape (shapes n a k)).PosDef∧
    ∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)≤ (4:ℝ) ^ k * (x ⬝ᵥ x):=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      rw [hid]
      exact ⟨Matrix.PosDef.one,by simp⟩
  | succ k ih =>
      have hne:realVector (a k) ≠ 0:=by
        intro h
        have hh:=ha k
        rw [h,dotProduct_zero] at hh
        norm_num at hh
      constructor
      · exact roundedStepShape_posDef n hn _ ih.1 _ hne _
          (gridDenominator_pos _ _ _) _ (stepAccuracy_pos n)
      · intro x
        have hs:=uniform_storedStep_bounds n hn (shapes n a k) ih.1 (a k) (ha k)
          (2 * k) (fun y => (ih.2 y).1) x
        have he:((2:ℝ) ^ (2 * (k + 1)))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ (2 * k))⁻¹:=by
          rw [show 2 * (k + 1)=2 * k + 2 by omega,pow_add]
          norm_num
        constructor
        · rw [he]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).1 (show (0:ℝ)≤ 1 / 4 by norm_num)
          change _≤ x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)
          nlinarith only [hh,hs.1]
        · change x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)≤ _
          rw [pow_succ]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).2 (show (0:ℝ)≤ 4 by norm_num)
          nlinarith only [hh,hs.2]

theorem shapes_shrink (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    Real.sqrt (realShape (shapes n a k)).det≤
      Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))):=by
  let v:=fun j => Real.sqrt (realShape (shapes n a j)).det
  have hstep:∀ j,v (j + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v j:=by
    intro j
    have hi:=shapes_invariant n hn a ha j
    exact uniform_storedStep_shrink n hn (shapes n a j) hi.1 (a j) (ha j)
      (2 * j) (fun x => (hi.2 x).1)
  have h:=EllipsoidStep.iterated_shrink_bound n v hstep k
  have hid:realShape (shapes n a 0)=1:=by
    ext i j
    simp [shapes,realShape,Matrix.one_apply,apply_ite]
  simpa only [v,hid,Matrix.det_one,Real.sqrt_one,mul_one] using h

theorem preserves_points_up_to (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (x:Fin n→ ℝ) (hx:(x - realVector c₀) ⬝ᵥ (x - realVector c₀)≤ 1)
    (k:ℕ)
    (hcut:∀ j < k,realVector (a j) ⬝ᵥ (x - realVector (centers n a c₀ j))≤ 0):
    (x - realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x - realVector (centers n a c₀ k)))≤ 1:=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      simpa only [centers,hid,inv_one,Matrix.one_mulVec] using hx
  | succ k ih =>
      have hi:=shapes_invariant n hn a ha k
      exact uniform_roundedStep_contains n hn (shapes n a k) hi.1 (a k) (centers n a c₀ k)
        (ha k) (2 * k) (2 * n + 4) (fun y => (hi.2 y).1) x
        (ih (fun j hj => hcut j (by omega))) (hcut k (by omega))

theorem sequence_grid_size (n k:ℕ):
    Nat.size (gridDenominator (2 * k + 2) (2 * n + 4) n)=2 * k + 3 * n + 10:=by
  rw [gridDenominator_size]
  omega

theorem shapes_below_threshold (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (B:ℕ):
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det <
      (((2:ℝ) ^ B)⁻¹) ^ n:=by
  have htarget:0 < (((2:ℝ) ^ B)⁻¹) ^ n:=by positivity
  have hlog:Real.log (2:ℝ)≤ 1:=by
    have h:=Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlogtarget:Real.log ((((2:ℝ) ^ B)⁻¹) ^ n) =
      -((B * n:ℕ):ℝ) * Real.log 2:=by
    rw [Real.log_pow,Real.log_inv,Real.log_pow]
    push_cast
    ring
  have he:-(thresholdSteps n B:ℝ) / (4 * ((n:ℝ) + 1)) =
      -(((B * n:ℕ):ℝ) + 1):=by
    have hp:(n:ℝ) + 1 ≠ 0:=by positivity
    unfold thresholdSteps
    push_cast
    field_simp
  have hlt:-(((B * n:ℕ):ℝ) + 1) < -((B * n:ℕ):ℝ) * Real.log 2:=by
    have h:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (B * n))
    linarith
  have h:=shapes_shrink n hn a ha (thresholdSteps n B)
  rw [he] at h
  apply h.trans_lt
  rw [← Real.exp_log htarget,hlogtarget]
  exact Real.exp_lt_exp.mpr hlt

end Lax109476Proofs.EllipsoidSequence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι:Type} [Fintype ι] [DecidableEq ι]

theorem quadratic_parallelogram (A:Matrix ι ι ℝ) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)):=by
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub]
  ring

theorem inverse_form_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    ∀ u:ι→ ℝ,u ⬝ᵥ (A⁻¹ *ᵥ u)≤ (r ^ 2)⁻¹ * (u ⬝ᵥ u):=by
  intro u
  by_cases hu:u=0
  · simp [hu]
  have hnorm:0 < u ⬝ᵥ u:=by
    simpa using (dotProduct_star_self_pos_iff (v:=u)).mpr hu
  let t:=r / Real.sqrt (u ⬝ᵥ u)
  let e:=t • u
  have ht:0 < t:=div_pos hr (Real.sqrt_pos.mpr hnorm)
  have hsq:(Real.sqrt (u ⬝ᵥ u)) ^ 2=u ⬝ᵥ u:=Real.sq_sqrt hnorm.le
  have he:e ⬝ᵥ e=r ^ 2:=by
    simp only [e,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    dsimp [t]
    field_simp
    nlinarith
  have hp:=hball e he.le
  have hm:=hball (-e) (by simpa using he.le)
  have hbase:0≤ (z - c) ⬝ᵥ (A⁻¹ *ᵥ (z - c)):=
    hA.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hid:=quadratic_parallelogram A⁻¹ (z - c) e
  have hp':((z - c) + e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) + e))≤ 1:=by
    have heq:(z - c) + e=z + e - c:=by abel_nf
    rw [heq]
    exact hp
  have hm':((z - c) - e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) - e))≤ 1:=by
    have heq:(z - c) - e=z + -e - c:=by abel_nf
    rw [heq]
    exact hm
  have hqe:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ 1:=by linarith
  have hqe':t ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ 1:=by
    simpa only [e,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,
      smul_eq_mul, ← mul_assoc, ← pow_two] using hqe
  have htform:t ^ 2=r ^ 2 / (u ⬝ᵥ u):=by
    dsimp [t]
    rw [div_pow,hsq]
  rw [htform,div_mul_eq_mul_div] at hqe'
  have hscale:r ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ u ⬝ᵥ u:=
    (div_le_one hnorm).mp hqe'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hscale)

theorem sqrt_det_lower_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    r ^ Fintype.card ι≤ Real.sqrt A.det:=by
  have hbound:=inverse_form_bound_of_ball hA z c r hr hball
  have hdet:=det_le_pow_of_form_bound hA.inv.posSemidef ((r ^ 2)⁻¹) hbound
  rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_pow] at hdet
  have ha:=hA.det_pos
  have hrpow:0 < (r ^ 2) ^ Fintype.card ι:=pow_pos (sq_pos_of_pos hr) _
  have hd:(r ^ 2) ^ Fintype.card ι≤ A.det:=(inv_le_inv₀ ha hrpow).mp hdet
  have hs:=Real.sq_sqrt ha.le
  have hsr:=Real.sqrt_nonneg A.det
  have hrr:(r ^ Fintype.card ι) ^ 2=(r ^ 2) ^ Fintype.card ι:=by ring
  nlinarith [pow_nonneg hr.le (Fintype.card ι)]

end Lax109476Proofs.EllipsoidBall

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidTermination

open Lax109476.RationalCertificates
open EllipsoidRounding EllipsoidSequence EllipsoidBall

theorem cannot_retain_ball (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (z:Fin n→ ℝ) (B:ℕ)
    (hunit:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector c₀) ⬝ᵥ (z + e - realVector c₀)≤ 1):
    ¬ ∀ k < thresholdSteps n B, ∀ e:Fin n→ ℝ,
      e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      realVector (a k) ⬝ᵥ (z + e - realVector (centers n a c₀ k))≤ 0:=by
  intro hcut
  let K:=thresholdSteps n B
  have hshape:=(shapes_invariant n hn a ha K).1
  have hball:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector (centers n a c₀ K)) ⬝ᵥ
        ((realShape (shapes n a K))⁻¹ *ᵥ (z + e - realVector (centers n a c₀ K)))≤ 1:=by
    intro e he
    exact preserves_points_up_to n hn a ha c₀ (z + e) (hunit e he) K
      (fun j hj => hcut j hj e he)
  have hlo:=sqrt_det_lower_bound_of_ball hshape z (realVector (centers n a c₀ K))
    (((2:ℝ) ^ B)⁻¹) (by positivity) hball
  have hhi:=shapes_below_threshold n hn a ha B
  simp only [Fintype.card_fin] at hlo
  exact (not_lt_of_ge hlo) hhi

end Lax109476Proofs.EllipsoidTermination

end

section

open scoped BigOperators

namespace Lax109476Proofs.EllipsoidStateSize

open Matrix EllipsoidBounds EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence RationalRounding RationalSizeBounds
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding

theorem entry_bound_of_form {n:ℕ} {A:Matrix (Fin n) (Fin n) ℝ}
    (hA:A.PosDef) (M:ℝ) (hM:0≤ M)
    (hupper:∀ x,x ⬝ᵥ (A *ᵥ x)≤ M * (x ⬝ᵥ x)) (i j:Fin n):
    |A i j|≤ M:=by
  let e:Fin n→ Fin n→ ℝ:=fun k => Pi.single k 1
  have hne:e j ≠ 0:=by
    intro h
    have hh:=congrFun h j
    simp [e] at hh
  have hcs:=form_cauchy_schwarz hA (e j) (e i) hne
  have hi:=hupper (e i)
  have hj:=hupper (e j)
  have hip:=hA.posSemidef.dotProduct_mulVec_nonneg (e i)
  have hjp:=hA.posSemidef.dotProduct_mulVec_nonneg (e j)
  simp [e,Matrix.mulVec,dotProduct,Pi.single_apply] at hcs hi hj hip hjp
  have hp:A j j * A i i≤ M * M:=mul_le_mul hj hi hip hM
  have hs:(A i j) ^ 2≤ M ^ 2:=by nlinarith only [hcs,hp]
  exact (sq_le_sq₀ (abs_nonneg _) hM).mp (by simpa only [sq_abs] using hs)

theorem shapes_entry_magnitude (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k:ℕ) (i j:Fin n):|(shapes n a k i j:ℝ)|≤ (4:ℝ) ^ k:=by
  have h:=shapes_invariant n hn a ha k
  exact entry_bound_of_form h.1 _ (by positivity) (fun x => (h.2 x).2) i j

theorem approximateCenter_displacement (n:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (M:ℝ) (hM:0≤ M)
    (hupper:∀ x,x ⬝ᵥ (realShape A *ᵥ x)≤ M ^ 2 * (x ⬝ᵥ x)) (i:Fin n):
    |(approximateCenter n A a c D i:ℝ) - (c i:ℝ)|≤ M:=by
  let q:=realVector a ⬝ᵥ (realShape A *ᵥ realVector a)
  let r:ℝ:=sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D
  let t:=(realShape A *ᵥ realVector a) i
  have hq:0 < q:=hA.dotProduct_mulVec_pos ha
  have hqRat:0≤ a ⬝ᵥ (A *ᵥ a):=by
    apply (Rat.cast_nonneg (K:=ℝ)).mp
    rw [cast_direction_form]
    exact hq.le
  have hr:Real.sqrt q≤ r:=by
    simpa only [cast_direction_form] using (sqrtUpper_bounds _ hqRat D hD).1
  have hrp:0 < r:=(Real.sqrt_pos.mpr hq).trans_le hr
  have hrsq:q≤ r ^ 2:=by nlinarith [Real.sqrt_nonneg q,Real.sq_sqrt hq.le]
  have hcs':=form_cauchy_schwarz hA (realVector a) (Pi.single i 1) ha
  have hii:=hupper (Pi.single i 1)
  simp [single_dotProduct,dotProduct_single] at hcs' hii
  have ht:t ^ 2≤ r ^ 2 * M ^ 2:=by
    have hmul:=mul_le_mul_of_nonneg_left hii hq.le
    have hmul':=mul_le_mul_of_nonneg_right hrsq (sq_nonneg M)
    dsimp [q,t] at *
    nlinarith only [hcs',hmul,hmul']
  have hab:|t|≤ r * M:=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hrp.le hM)).mp (by
      simpa only [sq_abs,mul_pow] using ht)
  have hn:(1:ℝ)≤ (n:ℝ) + 1:=by have:=(Nat.cast_nonneg n:(0:ℝ)≤ n); linarith
  have hden:0 < ((n:ℝ) + 1) * r:=by positivity
  have hb:|t / (((n:ℝ) + 1) * r)|≤ M:=by
    rw [abs_div,abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    exact hab.trans (by nlinarith [mul_nonneg hrp.le hM])
  have he:(approximateCenter n A a c D i:ℝ) - (c i:ℝ) =
      -(t / (((n:ℝ) + 1) * r)):=by
    simp [approximateCenter,realShape,realVector,Matrix.mulVec,dotProduct,
      Rat.cast_sum,r,t,smul_eq_mul,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [he,abs_neg]
  exact hb

theorem roundedCenter_displacement (n:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (M:ℝ) (hM:0≤ M)
    (hupper:∀ x,x ⬝ᵥ (realShape A *ᵥ x)≤ M ^ 2 * (x ⬝ᵥ x)) (i:Fin n):
    |(roundedCenter n A a c D i:ℝ) - (c i:ℝ)|≤ M + 1:=by
  have h:=approximateCenter_displacement n A hA a c ha D hD M hM hupper i
  have he:=roundDown_error (approximateCenter n A a c D i) D hD
  have hi:(1:ℝ) / D≤ 1:=by
    apply (div_le_one (by exact_mod_cast hD)).mpr
    exact_mod_cast hD
  have hround:|(roundedCenter n A a c D i:ℝ) -
      (approximateCenter n A a c D i:ℝ)|≤ 1:=by
    change |(roundDown (approximateCenter n A a c D i) D:ℝ) - _|≤ _
    rw [abs_sub_comm,abs_of_nonneg he.1]
    exact he.2.le.trans hi
  calc
    _≤ |(roundedCenter n A a c D i:ℝ) - (approximateCenter n A a c D i:ℝ)| +
      |(approximateCenter n A a c D i:ℝ) - (c i:ℝ)|:=abs_sub_le _ _ _
    _≤ _:=add_le_add hround h |>.trans_eq (add_comm _ _)

theorem centers_magnitude (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k:ℕ) (i:Fin n):|(centers n a 0 k i:ℝ)|≤ (2:ℝ) ^ (k + 2):=by
  induction k with
  | zero => simp [centers]
  | succ k ih =>
    have h:=shapes_invariant n hn a ha k
    have hne:realVector (a k) ≠ 0:=by
      intro he
      have hh:=ha k
      rw [he,dotProduct_zero] at hh
      norm_num at hh
    have hp:(4:ℝ) ^ k=((2:ℝ) ^ k) ^ 2:=by
      rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    have hd:=roundedCenter_displacement n (shapes n a k) h.1 (a k)
      (centers n a 0 k) hne (gridDenominator (2 * k + 2) (2 * n + 4) n)
      (gridDenominator_pos _ _ _) ((2:ℝ) ^ k)
      (by positivity) (fun x => by rw [← hp]; exact (h.2 x).2) i
    change |(roundedCenter n (shapes n a k) (a k) (centers n a 0 k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) i:ℝ)|≤ _
    have hab:=abs_sub_le (roundedCenter n (shapes n a k) (a k) (centers n a 0 k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) i:ℝ)
      (centers n a 0 k i:ℝ) 0
    simp only [sub_zero] at hab
    have hpow:1≤ (2:ℝ) ^ k:=one_le_pow₀ (by norm_num)
    rw [show k + 1 + 2=k + 3 by omega,pow_add]
    rw [show k + 2=k + 2 by rfl,pow_add] at ih
    norm_num only [show (2:ℝ) ^ 2=4 by norm_num,
      show (2:ℝ) ^ 3=8 by norm_num] at *
    linarith

def shapeGrid (n k:ℕ):ℕ:=
  gridDenominator (2 * k + 2) (2 * n + 4) n * (2 ^ (2 * n + 4)) ^ 2

theorem shapeGrid_pos (n k:ℕ):0 < shapeGrid n k:=by
  unfold shapeGrid
  exact Nat.mul_pos (gridDenominator_pos _ _ _) (by positivity)

theorem shapeGrid_size (n k:ℕ):(shapeGrid n k).size=2 * k + 7 * n + 18:=by
  unfold shapeGrid gridDenominator
  rw [← pow_mul, ← pow_add,Nat.size_pow]
  omega

theorem stored_shape_grid (n k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (i j:Fin n):
    ∃ z:ℤ,roundedStepShape n A a
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n) i j =
        (z:ℚ) / (shapeGrid n k:ℕ):=by
  let D:=gridDenominator (2 * k + 2) (2 * n + 4) n
  let S:=2 ^ (2 * n + 4)
  refine ⟨((S:ℤ) + 1) ^ 2 *
    (Int.floor (cutShape n A a i j * D) + if i=j then (n:ℤ) else 0), ?_⟩
  have hD:(D:ℚ) ≠ 0:=by exact_mod_cast ne_of_gt (gridDenominator_pos _ _ _)
  have hS:(S:ℚ) ≠ 0:=by dsimp [S]; positivity
  simp only [roundedStepShape,roundedShape,stepAccuracy,Matrix.smul_apply,
    Matrix.add_apply,Matrix.of_apply,Matrix.one_apply,smul_eq_mul,
    roundDown,Int.cast_mul,Int.cast_pow,Int.cast_add,Int.cast_natCast,
    Int.cast_one,Int.cast_ite,Int.cast_zero,shapeGrid,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat]
  have hScast:(2:ℚ) ^ (2 * n + 4)=(S:ℚ):=by simp [S]
  rw [hScast]
  change ((1 + 1 / (S:ℚ)) ^ 2) *
    ((Int.floor (cutShape n A a i j * D):ℚ) / D +
      (n:ℚ) / D * (if i=j then 1 else 0)) =
        (((S:ℚ) + 1) ^ 2 *
          ((Int.floor (cutShape n A a i j * D):ℚ) + if i=j then (n:ℚ) else 0)) /
          ((D:ℚ) * (S:ℚ) ^ 2)
  split_ifs <;> field_simp <;> ring

theorem shapes_denominator (n:ℕ) (a:ℕ→ Fin n→ ℚ) (k:ℕ) (i j:Fin n):
    (shapes n a (k + 1) i j).den≤ shapeGrid n k:=by
  obtain ⟨z,hz⟩:=stored_shape_grid n k (shapes n a k) (a k) i j
  change (roundedStepShape n (shapes n a k) (a k) _ _ i j).den≤ _
  rw [hz]
  exact (grid_num_den_bound z _ (shapeGrid_pos n k)).2

theorem numerator_bound_of_magnitude (q:ℚ) (M D:ℕ)
    (hm:|(q:ℝ)|≤ M) (hd:q.den≤ D):q.num.natAbs≤ M * D:=by
  have hnum:(q.num.natAbs:ℝ)=|(q:ℝ)| * (q.den:ℝ):=by
    rw [Nat.cast_natAbs,Int.cast_abs]
    have he:=congrArg (fun r:ℚ => (r:ℝ)) q.mul_den_eq_num
    simp only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast] at he
    rw [← he,abs_mul,abs_of_nonneg (a:=(q.den:ℝ)) (Nat.cast_nonneg _)]
  have hdR:(q.den:ℝ)≤ D:=by exact_mod_cast hd
  have h:=mul_le_mul hm hdR (Nat.cast_nonneg _) (Nat.cast_nonneg M)
  rw [← hnum] at h
  exact_mod_cast h

theorem encoding_bound_of_magnitude (q:ℚ) (M D:ℕ)
    (hm:|(q:ℝ)|≤ M) (hd:q.den≤ D):
    bitSize (encodeRational q)≤ 4 + M.size + 2 * D.size:=by
  have hn:=Nat.size_le_size (numerator_bound_of_magnitude q M D hm hd)
  have hmul:=size_mul_le M D
  have hds:=Nat.size_le_size hd
  have he:=EncodingSize.rational_size_upper q
  omega

theorem shapes_encoding_size (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ) (i j:Fin n):
    bitSize (encodeRational (shapes n a k i j))≤ 60 + 6 * k + 14 * n:=by
  cases k with
  | zero =>
    have h:=EncodingSize.rational_size_upper (shapes n a 0 i j)
    simp only [shapes,Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> norm_num at h <;> omega
  | succ k =>
    have hm:|(shapes n a (k + 1) i j:ℝ)|≤ (4 ^ (k + 1):ℕ):=by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using shapes_entry_magnitude n hn a ha (k + 1) i j
    have he:=encoding_bound_of_magnitude _ _ _ hm (shapes_denominator n a k i j)
    have hsizeM:(4 ^ (k + 1):ℕ).size=2 * (k + 1) + 1:=by
      rw [show (4:ℕ)=2 ^ 2 by decide, ← pow_mul,Nat.size_pow]
    rw [hsizeM,shapeGrid_size] at he
    omega

theorem centers_denominator (n:ℕ) (a:ℕ→ Fin n→ ℚ) (k:ℕ) (i:Fin n):
    (centers n a 0 (k + 1) i).den≤ gridDenominator (2 * k + 2) (2 * n + 4) n:=by
  exact (grid_num_den_bound _ _ (gridDenominator_pos _ _ _)).2

theorem centers_encoding_size (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ) (i:Fin n):
    bitSize (encodeRational (centers n a 0 k i))≤ 60 + 6 * k + 14 * n:=by
  cases k with
  | zero =>
    have h:=EncodingSize.rational_size_upper (centers n a 0 0 i)
    change bitSize (encodeRational 0)≤ _
    norm_num [centers] at h
    omega
  | succ k =>
    have hm:|(centers n a 0 (k + 1) i:ℝ)|≤ (2 ^ (k + 1 + 2):ℕ):=by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using centers_magnitude n hn a ha (k + 1) i
    have he:=encoding_bound_of_magnitude _ _ _ hm (centers_denominator n a k i)
    rw [Nat.size_pow,sequence_grid_size] at he
    omega

end Lax109476Proofs.EllipsoidStateSize

end

section

namespace Lax263307Proofs.ExhaustiveTargets

open Lax263307.ExhaustiveTargets

theorem candidate_complete (n k:ℕ) (I:Finset (Fin n)):
    I∈ candidates n k↔ I.card=k:=by
  constructor
  · intro hI
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hI
    obtain ⟨hsub,hlen⟩:=List.mem_sublistsLen.mp hl
    rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)),hlen]
  · intro hI
    let l:=(List.finRange n).filter fun v => decide (v∈ I)
    have hsub:List.Sublist l (List.finRange n):=List.filter_sublist
    have hnodup:l.Nodup:=hsub.nodup (List.nodup_finRange n)
    have heq:l.toFinset=I:=by ext v; simp [l]
    have hlen:l.length=k:=by rw [← List.toFinset_card_of_nodup hnodup,heq,hI]
    exact List.mem_map.mpr ⟨l,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,heq⟩

theorem search_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ):
    match findIndependentSet G k with
    | some I => G.IsIndepSet (I:Set (Fin n))∧ I.card=k
    | none => ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k:=by
  cases hsearch:findIndependentSet G k with
  | some I =>
    have hI:G.IsIndepSet (I:Set (Fin n)):=by
      simpa using List.find?_some hsearch
    exact ⟨hI, (Lax263307Proofs.ExhaustiveTargets.candidate_complete n k I).mp
      (List.mem_of_find?_eq_some hsearch)⟩
  | none =>
    intro J hJ
    by_contra hlarge
    obtain ⟨I,hIJ,hcard⟩:=Finset.exists_subset_card_eq (Nat.le_of_not_gt hlarge)
    have hI:G.IsIndepSet (I:Set (Fin n)):=hJ.mono (by simpa using hIJ)
    have hmem:=(Lax263307Proofs.ExhaustiveTargets.candidate_complete n k I).mpr hcard
    have hnone:=List.find?_eq_none.mp hsearch I hmem
    simp [hI] at hnone

end Lax263307Proofs.ExhaustiveTargets

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax263307.RoundedOracleSearch

open BufferedEllipsoid (scale)
open Lax109476.RationalEncoding (encodeRational)
open Lax759944.BinaryWordEncoding (bitSize)
open Matrix

def normalSchedule {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (k:ℕ):Fin n→ ℤ:=
  selectedNormal (oracle k (trajectory oracle k).2)

end Lax263307.RoundedOracleSearch

end

section

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open DistanceProjection

def Correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ):
    Outcome n→ Prop
  | .near y => PrimalFeasible (toReal P) (realVector y)∧
      ∀ j, |(y j:ℝ) - (center j:ℝ)|≤ (ρ:ℝ)
  | .far a α => (∑ j, |(a j:ℝ)|)≤ 1∧
      (∀ y,PrimalFeasible (toReal P) y→ (∑ j, (a j:ℝ) * y j)≤ (α:ℝ))∧
      (ρ:ℝ) < (∑ j, (a j:ℝ) * (center j:ℝ)) - (α:ℝ)
  | .reject => ¬ IsFeasible (toReal P)

end Lax263307.RationalProjection

end

section

namespace Lax263307.ProjectedOracle

open BufferedEllipsoid (scale)
open ComponentCutEncoding (coefficient)
open DistanceProjection (distanceProgram)
open MomentLP (Index decode dimension encode program)
open RationalCutBuffer (integerNormal)
open RationalProjection (classify)
open RegisteredLP (certificate)
open RoundedOracleSearch (Reply rationalNormal)
open LinearRelaxation AlgorithmParameters

def SearchCorrect {n:ℕ} (G:SimpleGraph (Fin n)) (k h D:ℕ):Option (Finset (Fin n))→ Prop
  | some I => Good G k h D I
  | none => IsIndependenceBound G Finset.univ (k-1)

end Lax263307.ProjectedOracle

end

section

namespace Lax263307.RecursiveAlgorithm

open ExhaustiveTargets (findIndependentSet)
open RecursionDepth (depth)
open ComputedSeparators AlgorithmParameters

def Correct {n:ℕ} (G:SimpleGraph (Fin n)) (k fuel D:ℕ):Option (Finset (Fin n))→ Prop
  | some I => G.IsIndepSet (I:Set (Fin n))∧ (1 - 4*(1/(D:ℝ)))^fuel * (k:ℝ)≤ I.card
  | none => ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k

end Lax263307.RecursiveAlgorithm

end

section

namespace Lax263307Proofs.ComputedSeparators

open scoped NNReal NNRat
open Lax263307.ComputedSeparators Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.VertexSplitting Lax263307.Entropy Lax263307.RepeatedCutAccounting
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow

def embedding {n:ℕ} (G:SimpleGraph (Fin n)) (R:Finset (Fin n)):restriction G R ↪g G where
  toFun:=label R
  inj':=(label R).injective
  map_rel_iff':=Iff.rfl

end Lax263307Proofs.ComputedSeparators

end

section

namespace Lax263307Proofs.RecursiveAlgorithm

open Lax263307.RecursiveAlgorithm Lax263307.ComputedSeparators
open Lax263307.GraphClasses Lax263307.AlgorithmParameters

theorem image_subset {n:ℕ} (C:Finset (Fin n)) (I:Finset (Fin C.card)):
    I.image (label C) ⊆ C:=by
  intro v hv
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
  exact C.orderEmbOfFin_mem rfl i

theorem image_independent {n:ℕ} (G:SimpleGraph (Fin n)) (C:Finset (Fin n))
    (I:Finset (Fin C.card)) (hI:(restriction G C).IsIndepSet (I:Set (Fin C.card))):
    G.IsIndepSet (I.image (label C):Set (Fin n)):=by
  intro u hu v hv huv
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hv
  exact hI hi hj (fun hij => huv (congrArg (label C) hij))

theorem restriction_bound {n:ℕ} (G:SimpleGraph (Fin n)) (C:Finset (Fin n)) (t:ℕ)
    (hbound:∀ I:Finset (Fin C.card), (restriction G C).IsIndepSet (I:Set (Fin C.card))→ I.card < t):
    Lax263307.LinearRelaxation.IsIndependenceBound G C (t-1):=by
  intro J hJC hJ
  let I:=Finset.univ.filter (fun i:Fin C.card => label C i∈ J)
  have heq:I.image (label C)=J:=by
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      have hcover:Finset.univ.image (label C)=C:=Finset.image_orderEmbOfFin_univ C rfl
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hcover.symm ▸ hJC hv)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi ▸ hv⟩,hi⟩
  have hI:(restriction G C).IsIndepSet (I:Set (Fin C.card)):=by
    intro i hi j hj hij
    exact hJ (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      ((label C).injective.ne hij)
  have hcard:I.card=J.card:=by
    rw [← heq,Finset.card_image_of_injective _ (label C).injective]
  have hh:=hbound I hI
  rw [hcard] at hh
  omega

theorem attempt_correct (C:GraphClass) (hereditary:IsHereditary C)
    (lp flow:List ℕ→ List ℕ) (a K B D:ℕ) (hD:4≤ D)
    (oracle:∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ 0 < n→ ∀ k h:ℕ,cutoff a K B n D < k→
      ∀ (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n))),
      Lax263307.NearOracle.ChildCorrect G D h child→
      Lax263307.ProjectedOracle.SearchCorrect G k h D
        (Lax263307.ProjectedOracle.search lp flow a K B D G k child))
    (fuel:ℕ) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG:G∈ C n) (hdepth:Lax263307.RecursionDepth.depth n≤ fuel) (k:ℕ):
    Correct G k fuel D (attempt lp flow a K B D fuel G k):=by
  have hDpos:(0:ℝ) < D:=Nat.cast_pos.mpr (by omega)
  have hβ:0≤ 1 - 4*(1/(D:ℝ))∧ 1 - 4*(1/(D:ℝ))≤ 1:=by
    have hd:(4:ℝ)≤ D:=Nat.cast_le.mpr hD
    constructor
    · apply sub_nonneg.mpr
      rw [mul_one_div,div_le_one hDpos]
      exact hd
    · have:(0:ℝ)≤ 4*(1/(D:ℝ)):=by positivity
      linarith
  induction fuel generalizing n k with
  | zero =>
    unfold attempt
    split_ifs with hsmall hlarge
    · have hh:=Lax263307Proofs.ExhaustiveTargets.search_correct G k
      cases he:Lax263307.ExhaustiveTargets.findIndependentSet G k with
      | none => rw [he] at hh; exact hh
      | some I =>
        rw [he] at hh
        exact ⟨hh.1,by simp [hh.2]⟩
    · intro J _
      have hj:J.card≤ n:=by simpa using Finset.card_le_univ J
      omega
    · have hn:1 < n:=by omega
      rw [Lax263307.RecursionDepth.depth,if_neg (by omega)] at hdepth
      omega
  | succ fuel ih =>
    unfold attempt
    split_ifs with hsmall hlarge
    · have hh:=Lax263307Proofs.ExhaustiveTargets.search_correct G k
      cases he:Lax263307.ExhaustiveTargets.findIndependentSet G k with
      | none => rw [he] at hh; exact hh
      | some I =>
        rw [he] at hh
        refine ⟨hh.1, ?_⟩
        have hp:=pow_le_one₀ (n:=fuel+1) hβ.1 hβ.2
        have hm:=mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg k:(0:ℝ)≤ k)
        simpa [hh.2] using hm
    · intro J _
      have hj:J.card≤ n:=by simpa using Finset.card_le_univ J
      omega
    · have hn:1 < n:=by omega
      let child:=fun (S:Finset (Fin n)) t =>
        (attempt lp flow a K B D fuel (restriction G S) t).map (fun I => I.image (label S))
      have hc:Lax263307.NearOracle.ChildCorrect G D fuel child:=by
        intro S hS t
        have hclass:=hereditary S.card n (restriction G S) G hG
          ⟨Lax263307Proofs.ComputedSeparators.embedding G S⟩
        have hdep:=Lax263307Proofs.RecursionDepth.balanced_decrease n S.card hn hS
        have hh:=ih (restriction G S) hclass (by omega) t
        dsimp only [child]
        cases he:attempt lp flow a K B D fuel (restriction G S) t with
        | some I =>
          rw [he] at hh
          change _∧ _∧ _
          refine ⟨image_subset S I,image_independent G S I hh.1, ?_⟩
          rw [Finset.card_image_of_injective _ (label S).injective]
          exact hh.2
        | none =>
          rw [he] at hh
          exact restriction_bound G S t hh
      have hh:=oracle n G hG (by omega) k fuel (by omega) child hc
      change Correct G k (fuel+1) D (Lax263307.ProjectedOracle.search lp flow a K B D G k child)
      cases he:Lax263307.ProjectedOracle.search lp flow a K B D G k child with
      | some I =>
        rw [he] at hh
        exact hh
      | none =>
        rw [he] at hh
        intro J hJ
        have hb:=hh J (Finset.subset_univ J) hJ
        have hk:0 < k:=by omega
        omega

open Lax263307.PowerBagBounds

end Lax263307Proofs.RecursiveAlgorithm

end

section

namespace Lax263307Proofs.BufferedEllipsoid

open Matrix Lax263307.BufferedEllipsoid

theorem coordinate_ball_bound {n:ℕ} (e:Fin n→ ℝ) (ρ:ℝ) (nonnegative:0≤ ρ)
    (ball:e ⬝ᵥ e≤ ρ ^ 2):∀ i, |e i|≤ ρ:=by
  intro i
  have h:(e i) ^ 2≤ ∑ j, (e j) ^ 2:=
    Finset.single_le_sum (fun j _ => sq_nonneg (e j)) (Finset.mem_univ i)
  have hs:(e i) ^ 2≤ ρ ^ 2:=h.trans (by simpa only [dotProduct,pow_two] using ball)
  simpa only [abs_of_nonneg nonnegative] using (sq_le_sq).mp hs

theorem scaled_cube_norm {n:ℕ} (positive:0 < n) (z:Fin n→ ℝ)
    (cube:∀ i,0≤ z i∧ z i≤ 1):scale z ⬝ᵥ scale z≤ (1 / 16:ℝ):=by
  have hn:(0:ℝ) < n:=by exact_mod_cast positive
  have hn1:(1:ℝ)≤ n:=by exact_mod_cast positive
  have each (i:Fin n):(scale z i) ^ 2≤ (1 / (4 * (n:ℝ))) ^ 2:=by
    have hlow:0≤ scale z i:=div_nonneg (cube i).1 (by positivity)
    have hhigh:scale z i≤ 1 / (4 * (n:ℝ)):=div_le_div_of_nonneg_right (cube i).2 (by positivity)
    exact pow_le_pow_left₀ hlow hhigh 2
  have hsum:=Finset.sum_le_sum (fun i (_:i∈ (Finset.univ:Finset (Fin n))) => each i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have heq:(n:ℝ) * (1 / (4 * (n:ℝ))) ^ 2=1 / (16 * n):=by field_simp; ring
  have hbound:1 / (16 * (n:ℝ))≤ (1 / 16:ℝ):=by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  simpa only [dotProduct,pow_two] using hsum.trans (heq.le.trans hbound)

theorem initial_ball {n:ℕ} (positive:0 < n) (z:Fin n→ ℝ)
    (cube:∀ i,0≤ z i∧ z i≤ 1) (ρ:ℝ) (nonnegative:0≤ ρ) (small:ρ≤ 1 / 4)
    (e:Fin n→ ℝ) (ball:e ⬝ᵥ e≤ ρ ^ 2):
    (scale z + e) ⬝ᵥ (scale z + e)≤ 1:=by
  have hscale:=Lax263307Proofs.BufferedEllipsoid.scaled_cube_norm positive z cube
  have hr:ρ ^ 2≤ (1 / 16:ℝ):=by nlinarith
  have hs:=Finset.sum_le_sum (fun i (_:i∈ (Finset.univ:Finset (Fin n))) =>
    show (scale z i + e i) ^ 2≤ 2 * (scale z i) ^ 2 + 2 * (e i) ^ 2 from by
      nlinarith [sq_nonneg (scale z i - e i)])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hs':(scale z + e) ⬝ᵥ (scale z + e)≤ 2 * (scale z ⬝ᵥ scale z) + 2 * (e ⬝ᵥ e):=by
    simpa only [dotProduct,pow_two,Pi.add_apply] using hs
  linarith

theorem integer_normal_norm {n:ℕ} (a:Fin n→ ℤ) (nonzero:∃ i,a i ≠ 0):
    1≤ (fun i => (a i:ℝ)) ⬝ᵥ (fun i => (a i:ℝ)):=by
  obtain ⟨i,hi⟩:=nonzero
  have hs:(0:ℤ) < (a i) ^ 2:=sq_pos_of_ne_zero hi
  have hsi:(1:ℤ)≤ (a i) ^ 2:=by omega
  have hsr:(1:ℝ)≤ (a i:ℝ) ^ 2:=by exact_mod_cast hsi
  have hsum:=Finset.single_le_sum (fun j (_:j∈ (Finset.univ:Finset (Fin n))) =>
    sq_nonneg (a j:ℝ)) (Finset.mem_univ i)
  exact hsr.trans (by simpa only [dotProduct,pow_two] using hsum)

end Lax263307Proofs.BufferedEllipsoid

end

section

namespace Lax263307Proofs.RoundedOracleSearch

open Matrix Lax263307.RoundedOracleSearch
open Lax109476.RationalCertificates

theorem cached_eq {n:ℕ} (state:State n):cached state=state:=by
  apply Prod.ext
  · funext i j
    simp [cached,Vector.get]
    rfl
  · funext i
    simp [cached,Vector.get]
    rfl

theorem scan_sound {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (Good:Result→ Prop)
    (answers:∀ k center answer,oracle k center=.found answer→ Good answer)
    (count k:ℕ) (state:State n) (answer:Result)
    (found:scan oracle k count state=some answer):Good answer:=by
  induction count generalizing k state with
  | zero => simp [scan] at found
  | succ count ih =>
    cases hreply:oracle k state.2 with
    | found result =>
      have heq:result=answer:=by simpa only [scan,hreply,Option.some.injEq] using found
      subst answer
      exact answers k state.2 result hreply
    | reject => simp [scan,hreply] at found
    | cut a =>
      apply ih (k + 1) (update k state a)
      simpa only [scan,hreply] using found

theorem search_sound {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (B:ℕ) (Good:Result→ Prop)
    (answers:∀ k center answer,oracle k center=.found answer→ Good answer):
    ∀ answer,search oracle B=some answer→ Good answer:=by
  intro answer found
  exact scan_sound oracle Good answers (steps n B) 0 (1,0) answer found

theorem scan_failure {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (no_reject:∀ k center,oracle k center ≠ .reject) (count k:ℕ)
    (failed:scan oracle k count (trajectory oracle k)=none):
    ∀ j,k≤ j→ j < k + count→ ∃ a,oracle j (trajectory oracle j).2=.cut a:=by
  induction count generalizing k with
  | zero => intro j hj hj'; omega
  | succ count ih =>
    cases hreply:oracle k (trajectory oracle k).2 with
    | found answer => simp [scan,hreply] at failed
    | reject => exact False.elim (no_reject k _ hreply)
    | cut a =>
      have hnext:trajectory oracle (k + 1)=update k (trajectory oracle k) a:=by
        simp only [trajectory,hreply,selectedNormal]
      have htail:scan oracle (k + 1) count (trajectory oracle (k + 1))=none:=by
        rw [hnext]
        simpa only [scan,hreply] using failed
      intro j hj hj'
      by_cases heq:j=k
      · subst j
        exact ⟨a,hreply⟩
      · exact ih (k + 1) htail j (by omega) (by omega)

theorem schedule_norm {n:ℕ} {Result:Type} (positive:0 < n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i ≠ 0) (k:ℕ):
    1≤ realVector (rationalNormal (normalSchedule oracle k)) ⬝ᵥ
      realVector (rationalNormal (normalSchedule oracle k)):=by
  have hnormal:∃ i,normalSchedule oracle k i ≠ 0:=by
    unfold normalSchedule
    cases hreply:oracle k (trajectory oracle k).2 with
    | cut a => exact nonzero k _ a hreply
    | found answer => exact ⟨⟨0,positive⟩,by simp [selectedNormal,fallback]⟩
    | reject => exact ⟨⟨0,positive⟩,by simp [selectedNormal,fallback]⟩
  have hcast:realVector (rationalNormal (normalSchedule oracle k)) =
      (fun i => (normalSchedule oracle k i:ℝ)):=by
    funext i
    simp [realVector,rationalNormal]
  rw [hcast]
  exact Lax263307Proofs.BufferedEllipsoid.integer_normal_norm (normalSchedule oracle k) hnormal

theorem trajectory_eq_sequences {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (k:ℕ):
    (trajectory oracle k).1=Lax109476Proofs.EllipsoidSequence.shapes n
      (fun j => rationalNormal (normalSchedule oracle j)) k∧
    (trajectory oracle k).2=Lax109476Proofs.EllipsoidSequence.centers n
      (fun j => rationalNormal (normalSchedule oracle j)) 0 k:=by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    change (update k (trajectory oracle k) (normalSchedule oracle k)).1=_∧
      (update k (trajectory oracle k) (normalSchedule oracle k)).2=_
    simp only [update,cached_eq]
    change Lax109476Proofs.EllipsoidCenter.roundedStepShape n (trajectory oracle k).1
        (rationalNormal (normalSchedule oracle k))
        (Lax109476Proofs.EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n)
        (Lax109476Proofs.EllipsoidIteration.stepAccuracy n)=_∧
      Lax109476Proofs.EllipsoidCenter.roundedCenter n (trajectory oracle k).1
        (rationalNormal (normalSchedule oracle k)) (trajectory oracle k).2
        (Lax109476Proofs.EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n)=_
    simp only [Lax109476Proofs.EllipsoidSequence.shapes,Lax109476Proofs.EllipsoidSequence.centers]
    rw [ih.1,ih.2]
    exact ⟨rfl,rfl⟩

theorem search_complete {n:ℕ} {Result:Type} (dimension:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (B:ℕ) (precision:2≤ B)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i ≠ 0)
    (no_reject:∀ k center,oracle k center ≠ .reject)
    (z:Fin n→ ℝ) (cube:∀ i,0≤ z i∧ z i≤ 1)
    (retains:∀ k center a,oracle k center=.cut a→
      ∀ e:Fin n→ ℝ, (∀ i, |e i|≤ ((2:ℝ) ^ B)⁻¹)→
        (fun i => (a i:ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale z + e - (fun i => (center i:ℝ)))≤ 0):
    ∃ answer,search oracle B=some answer:=by
  by_contra hfound
  have hnone:search oracle B=none:=by
    cases h:search oracle B with
    | none => rfl
    | some answer => exact False.elim (hfound ⟨answer,h⟩)
  have hcuts:=scan_failure oracle no_reject (steps n B) 0 hnone
  let a:ℕ→ Fin n→ ℚ:=fun k => rationalNormal (normalSchedule oracle k)
  let ρ:ℝ:=((2:ℝ) ^ B)⁻¹
  have hρ:0≤ ρ:=by dsimp [ρ]; positivity
  have hsmall:ρ≤ 1 / 4:=by
    have hp:(4:ℝ)≤ (2:ℝ) ^ B:=by
      have h:=pow_le_pow_right₀ (show (1:ℝ)≤ 2 by norm_num) precision
      norm_num at h
      exact h
    dsimp [ρ]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num:(0:ℝ) < 4) hp
  apply Lax109476Proofs.EllipsoidTermination.cannot_retain_ball n dimension a
    (fun k => schedule_norm (by omega) oracle nonzero k) 0
    (Lax263307.BufferedEllipsoid.scale z) B
  · intro e he
    have h:=Lax263307Proofs.BufferedEllipsoid.initial_ball (by omega) z cube ρ hρ hsmall e he
    have hzero:realVector (0:Fin n→ ℚ)=0:=by funext i; simp [realVector]
    rw [hzero]
    simpa only [sub_zero] using h
  · intro k hk e he
    obtain ⟨normal,hreply⟩:=hcuts k (by omega)
      (by simpa only [Lax109476Proofs.EllipsoidSequence.thresholdSteps,steps,Nat.zero_add] using hk)
    have hnormal:a k=rationalNormal normal:=by
      simp only [a,normalSchedule,hreply,selectedNormal]
    rw [hnormal]
    have h:=retains k (trajectory oracle k).2 normal hreply e
      (Lax263307Proofs.BufferedEllipsoid.coordinate_ball_bound e ρ hρ he)
    rw [(trajectory_eq_sequences oracle k).2] at h
    have hcast:realVector (rationalNormal normal)=(fun i => (normal i:ℝ)):=by
      funext i
      simp [realVector,rationalNormal]
    rw [hcast]
    exact h

theorem center_encoding_bound {n:ℕ} {Result:Type} (dimension:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i ≠ 0) (k:ℕ) (i:Fin n):
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational ((trajectory oracle k).2 i))≤ 60 + 6 * k + 14 * n:=by
  rw [(trajectory_eq_sequences oracle k).2]
  exact Lax109476Proofs.EllipsoidStateSize.centers_encoding_size n dimension
    (fun j => rationalNormal (normalSchedule oracle j))
    (fun j => schedule_norm (by omega) oracle nonzero j) k i

theorem shape_encoding_bound {n:ℕ} {Result:Type} (dimension:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i ≠ 0)
    (k:ℕ) (i j:Fin n):
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational ((trajectory oracle k).1 i j))≤ 60 + 6 * k + 14 * n:=by
  rw [(trajectory_eq_sequences oracle k).1]
  exact Lax109476Proofs.EllipsoidStateSize.shapes_encoding_size n dimension
    (fun j => rationalNormal (normalSchedule oracle j))
    (fun j => schedule_norm (by omega) oracle nonzero j) k i j

end Lax263307Proofs.RoundedOracleSearch

end

section

namespace Lax263307Proofs.ProjectedOracle

open Matrix
open Lax263307.ProjectedOracle Lax263307.AlgorithmParameters
open Lax263307.LinearRelaxation Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem search_correct {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K B D:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k h:ℕ)
    (hn:0 < n) (hk:0 < k)
    (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n)))
    (oracle_correct:∀ center,Correct G k h a K B D center (run lp flow a K B D G k child center)):
    SearchCorrect G k h D (search lp flow a K B D G k child):=by
  let oracle:=fun (_:ℕ) center => run lp flow a K B D G k child center
  have hs:∀ I,Lax263307.RoundedOracleSearch.search oracle (precision a K B n D)=some I→ Good G k h D I:=by
    apply Lax263307Proofs.RoundedOracleSearch.search_sound
    intro t center I he
    have hh:=oracle_correct center
    change Correct G k h a K B D center (oracle t center) at hh
    rw [he] at hh
    exact hh
  cases hout:search lp flow a K B D G k child with
  | some I => exact hs I hout
  | none =>
    intro J _ hJ
    by_contra hlarge
    have hsize:k≤ J.card:=by omega
    obtain ⟨I,hIJ,hcard⟩:=Finset.exists_subset_card_eq hsize
    have hI:G.IsIndepSet (I:Set (Fin n)):=hJ.mono (by simpa using hIJ)
    have hmem:indicator (level a K B n D) I∈ independentSetHull G k (level a K B n D):=
      subset_convexHull ℝ _ ⟨I,hI,hcard,rfl⟩
    have hnz:∀ t center normal,oracle t center=.cut normal→ ∃ i,normal i ≠ 0:=by
      intro t center normal he
      have hh:=oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      exact hh.1
    have hno:∀ t center,oracle t center ≠ .reject:=by
      intro t center he
      have hh:=oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      change independentSetHull G k (level a K B n D)=∅ at hh
      rw [hh] at hmem
      exact hmem
    have hretain:∀ t center normal,oracle t center=.cut normal→
        ∀ e:Index n (level a K B n D)→ ℝ,
        (∀ i, |e i|≤ ((2:ℝ)^precision a K B n D)⁻¹)→
        (fun i => (normal i:ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale (encode (indicator (level a K B n D) I)) + e -
            (fun i => (center i:ℝ)))≤ 0:=by
      intro t center normal he e he'
      have hh:=oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      exact hh.2 _ hmem e he'
    have hcube:∀ i:Index n (level a K B n D),
        0≤ encode (indicator (level a K B n D) I) i∧ encode (indicator (level a K B n D) I) i≤ 1:=by
      intro i
      simp only [encode,indicator]
      split_ifs <;> norm_num
    obtain ⟨answer,hans⟩:=Lax263307Proofs.RoundedOracleSearch.search_complete
      (Lax263307Proofs.CoordinateCatalog.catalog_two n (level a K B n D) hn) oracle
      (precision a K B n D) (by unfold precision; omega) hnz hno _ hcube hretain
    change search lp flow a K B D G k child=some answer at hans
    rw [hout] at hans
    contradiction

open Lax263307.GraphClasses Lax263307.PowerBagBounds

end Lax263307Proofs.ProjectedOracle

end

section

namespace Lax263307Proofs.NativeTrajectoryResources

open Lax263307 RoundedOracleSearch Matrix
open Lax109476.RationalEncoding Lax109476.RationalCertificates Lax109476Proofs.EllipsoidRounding
open Lax759944.BinaryWordEncoding

theorem height_of_encoding (q:ℚ) (h:ℕ) (hh:bitSize (encodeRational q)≤ h):
    NativeRoundedStep.height q h:=by
  have hn:=Lax455465Proofs.WordSize.member_bound (encodeRational q) q.num.natAbs
    (by simp [encodeRational])
  have hd:=Lax455465Proofs.WordSize.member_bound (encodeRational q) q.den
    (by simp [encodeRational])
  exact ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) hh),
    hd.le.trans (Nat.pow_le_pow_right (by decide) hh)⟩

theorem state_height {n:ℕ} {Result:Type} (hn:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i≠0)
    (R k:ℕ) (hnR:n≤ R) (hkR:k≤ R):
    (∀ i j,NativeRoundedStep.height ((trajectory oracle k).1 i j) (80*(R+1)))∧
    (∀ i,NativeRoundedStep.height ((trajectory oracle k).2 i) (80*(R+1))):=by
  constructor
  · intro i j
    apply height_of_encoding
    exact (Lax263307Proofs.RoundedOracleSearch.shape_encoding_bound hn oracle nonzero k i j).trans (by omega)
  · intro i
    apply height_of_encoding
    exact (Lax263307Proofs.RoundedOracleSearch.center_encoding_bound hn oracle nonzero k i).trans (by omega)

theorem shape_posDef {n:ℕ} {Result:Type} (hn:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i≠0) (k:ℕ):
    (realShape (trajectory oracle k).1).PosDef:=by
  rw [(Lax263307Proofs.RoundedOracleSearch.trajectory_eq_sequences oracle k).1]
  exact (Lax109476Proofs.EllipsoidSequence.shapes_invariant n hn
    (fun j => rationalNormal (normalSchedule oracle j))
    (fun j => Lax263307Proofs.RoundedOracleSearch.schedule_norm (by omega) oracle nonzero j) k).1

theorem update_positive {n:ℕ} {Result:Type} (hn:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i≠0)
    (k:ℕ) (a:Fin n→ ℤ) (ha:oracle k (trajectory oracle k).2=.cut a):
    0< rationalNormal a ⬝ᵥ ((trajectory oracle k).1 *ᵥ rationalNormal a):=by
  have hne:realVector (rationalNormal a)≠0:=by
    obtain ⟨i,hi⟩:=nonzero k _ a ha
    intro he
    have hi0:=congrFun he i
    have:a i=0:=by simpa [realVector,rationalNormal] using hi0
    exact hi this
  have hpos:(0:ℝ)< realVector (rationalNormal a) ⬝ᵥ
      (realShape (trajectory oracle k).1 *ᵥ realVector (rationalNormal a)):=by
    simpa using (shape_posDef hn oracle nonzero k).dotProduct_mulVec_pos hne
  have hcast:((rationalNormal a ⬝ᵥ ((trajectory oracle k).1 *ᵥ rationalNormal a):ℚ):ℝ)=
      realVector (rationalNormal a) ⬝ᵥ (realShape (trajectory oracle k).1 *ᵥ realVector (rationalNormal a)):=by
    simp [dotProduct,mulVec,realVector,realShape]
  rw [←hcast] at hpos
  exact_mod_cast hpos

end Lax263307Proofs.NativeTrajectoryResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem search_correct {C:GraphClass} {lp flow:List ℕ→ List ℕ} {a K b:ℕ}
    (ho:OracleCorrect C lp flow a K b) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG:G∈ C n) (hn:0< n) (D k h:ℕ) (hD:4≤ D) (hlarge:cutoff a K b n D< k)
    (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n))) (hc:NearOracle.ChildCorrect G D h child):
    ProjectedOracle.SearchCorrect G k h D (ProjectedOracle.search lp flow a K b D G k child):=by
  exact Lax263307Proofs.ProjectedOracle.search_correct lp flow a K b D G k h hn (by omega) child
    (ho n G hG hn D k h hD hlarge child hc)

theorem child_correct {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} {a K b:ℕ} (ho:OracleCorrect C lp flow a K b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG:G∈ C n) (hn:1< n)
    (D fuel:ℕ) (hD:4≤ D) (hdepth:RecursionDepth.depth n≤ fuel+1):
    NearOracle.ChildCorrect G D fuel (child lp flow a K b D fuel G):=by
  intro S hS t
  have hclass:=hereditary S.card n (restriction G S) G hG
    ⟨Lax263307Proofs.ComputedSeparators.embedding G S⟩
  have hdep:=Lax263307Proofs.RecursionDepth.balanced_decrease n S.card hn hS
  have hh:=Lax263307Proofs.RecursiveAlgorithm.attempt_correct C hereditary lp flow a K b D hD
    (fun m H _ hH hm j h hj query hquery => search_correct ho H hH hm D j h hD hj query hquery)
    fuel (restriction G S) hclass (by omega) t
  dsimp only [child]
  cases he:RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t with
  | some I =>
    rw [he] at hh
    change _∧ _∧ _
    refine ⟨Lax263307Proofs.RecursiveAlgorithm.image_subset S I,
      Lax263307Proofs.RecursiveAlgorithm.image_independent G S I hh.1,?_⟩
    rw [Finset.card_image_of_injective _ (label S).injective]
    exact hh.2
  | none =>
    rw [he] at hh
    exact Lax263307Proofs.RecursiveAlgorithm.restriction_bound G S t hh

theorem cut_nonzero {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} {a K b:ℕ} (ho:OracleCorrect C lp flow a K b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG:G∈ C n) (hn:1< n)
    (D k fuel:ℕ) (hD:4≤ D) (hlarge:cutoff a K b n D< k) (hdepth:RecursionDepth.depth n≤ fuel+1):
    ∀ j center normal, (fun (_:ℕ) center => ProjectedOracle.run lp flow a K b D G k
      (child lp flow a K b D fuel G) center) j center=RoundedOracleSearch.Reply.cut normal→
      ∃ i,normal i≠0:=by
  intro j center normal he
  have hc:=ho n G hG (by omega) D k fuel hD hlarge _ (child_correct hereditary ho G hG hn D fuel hD hdepth) center
  dsimp only at he
  rw [he] at hc
  exact hc.1

theorem trajectory_guards {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} {a K b:ℕ} (ho:OracleCorrect C lp flow a K b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG:G∈ C n) (hn:1< n)
    (D k fuel R j:ℕ) (hD:4≤ D) (hlarge:cutoff a K b n D< k)
    (hdepth:RecursionDepth.depth n≤ fuel+1) (hN:MomentLP.dimension n (level a K b n D)≤ R) (hj:j≤ R):
    let oracle:=fun (_:ℕ) center => ProjectedOracle.run lp flow a K b D G k
      (child lp flow a K b D fuel G) center
    (∀ i l,NativeRoundedStep.height ((RoundedOracleSearch.trajectory oracle j).1 i l) (80*(R+1)))∧
    (∀ i,NativeRoundedStep.height ((RoundedOracleSearch.trajectory oracle j).2 i) (80*(R+1)))∧
    ∀ normal,oracle j (RoundedOracleSearch.trajectory oracle j).2=.cut normal→
      0< dotProduct (RoundedOracleSearch.rationalNormal normal)
        ((RoundedOracleSearch.trajectory oracle j).1 *ᵥ RoundedOracleSearch.rationalNormal normal):=by
  dsimp only
  let oracle:=fun (_:ℕ) center => ProjectedOracle.run lp flow a K b D G k
    (child lp flow a K b D fuel G) center
  have hdim:=Lax263307Proofs.CoordinateCatalog.catalog_two n (level a K b n D) (by omega:0< n)
  have hnz:=cut_nonzero hereditary ho G hG hn D k fuel hD hlarge hdepth
  have heights:=NativeTrajectoryResources.state_height hdim oracle hnz R j hN hj
  exact ⟨heights.1,heights.2,fun normal he => NativeTrajectoryResources.update_positive hdim oracle hnz j normal he⟩

end Lax263307Proofs.NativeRecursiveOracle

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} {a K b:Nat},
      Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow a K b→
        ∀ {n:Nat} (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
          @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n))) (@Set.instMembership (SimpleGraph (Fin n)))
              (C n) G→
            Nat.lt ((1:Nat)) n→
              ∀ (D k fuel R j:Nat),
                Nat.le ((4:Nat)) D→
                  Nat.lt (Lax263307.AlgorithmParameters.cutoff a K b n D) k→
                    Nat.le (Lax263307.RecursionDepth.depth n)
                        (Nat.add fuel
                          ((1:Nat)))→
                      Nat.le
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) R→
                        Nat.le j R→
                          have oracle:=
                            fun (x:Nat)
                              (center:
                                Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D)→ Rat) =>
                            @Lax263307.ProjectedOracle.run n lp flow a K b D G inst k
                              (@Lax263307Proofs.NativeRecursiveOracle.child n lp flow a K b D fuel G inst) center;
                          And
                            (∀
                              (i l:
                                Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))),
                              Lax263307.NativeRoundedStep.height
                                (@Prod.fst
                                  (Matrix
                                    (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)))
                                    (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)))
                                    Rat)
                                  (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))→
                                    Rat)
                                  (@Lax263307.RoundedOracleSearch.trajectory
                                    (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                    (Finset (Fin n)) oracle j)
                                  i l)
                                (Nat.mul
                                  ((80:Nat))
                                  (Nat.add R
                                    ((1:Nat)))))
                            (And
                              (∀
                                (i:
                                  Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))),
                                Lax263307.NativeRoundedStep.height
                                  (@Prod.snd
                                    (Matrix
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat)
                                    (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D))→
                                      Rat)
                                    (@Lax263307.RoundedOracleSearch.trajectory
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)) oracle j)
                                    i)
                                  (Nat.mul
                                    ((80:Nat))
                                    (Nat.add R
                                      ((1:Nat)))))
                              (∀
                                (normal:
                                  Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))→
                                    Int),
                                @Eq
                                    (Lax263307.RoundedOracleSearch.Reply
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)))
                                    (oracle j
                                      (@Prod.snd
                                        (Matrix
                                          (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)))
                                          (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)))
                                          Rat)
                                        (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))→
                                          Rat)
                                        (@Lax263307.RoundedOracleSearch.trajectory
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)) oracle j)))
                                    (@Lax263307.RoundedOracleSearch.Reply.cut
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)) normal)→
                                  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                    (@dotProduct
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat
                                      (Fin.fintype
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat.instMul Rat.addCommMonoid
                                      (@Lax263307.RoundedOracleSearch.rationalNormal
                                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                        normal)
                                      (@Matrix.mulVec
                                        (Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        (Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        Rat
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                                              (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                                        (Fin.fintype
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        (@Prod.fst
                                          (Matrix
                                            (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)))
                                            (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)))
                                            Rat)
                                          (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D))→
                                            Rat)
                                          (@Lax263307.RoundedOracleSearch.trajectory
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))
                                            (Finset (Fin n)) oracle j))
                                        (@Lax263307.RoundedOracleSearch.rationalNormal
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          normal))))):= @Lax263307Proofs.NativeRecursiveOracle.trajectory_guards

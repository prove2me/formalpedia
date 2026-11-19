-- Prove2me | solution 1 for Lax263307Proofs.NativeRootResource.uniform_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:18:09.038407+00:00
-- url     : https://prove2.me/submissions/367b4d9a-0ceb-41f7-a7b3-80e653fcac7f

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces

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

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning

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

theorem candidate_count (n r:ℕ):
    (candidates n r).length=∑ j∈ Finset.range (r + 1),n.choose j:=by
  induction r with
  | zero => simp [candidates,List.sublistsLen_zero]
  | succ r ih =>
    have hrec:(candidates n (r + 1)).length =
        (candidates n r).length + n.choose (r + 1):=by
      simp [candidates,List.range_succ,List.flatMap_append,List.length_sublistsLen,Nat.add_assoc]
    calc
      (candidates n (r + 1)).length =
          (∑ j∈ Finset.range (r + 1),n.choose j) + n.choose (r + 1):=by rw [hrec,ih]
      _=∑ j∈ Finset.range (r + 1 + 1),n.choose j:=
        (Finset.sum_range_succ (fun j => n.choose j) (r + 1)).symm

theorem candidate_bound (n r:ℕ):(candidates n r).length≤ (r + 1) * (n + 1) ^ r:=by
  rw [candidate_count]
  calc
    (∑ j∈ Finset.range (r + 1),n.choose j)≤
        ∑ _j∈ Finset.range (r + 1), (n + 1) ^ r:=by
      apply Finset.sum_le_sum
      intro j hj
      have hjr:j≤ r:=by have:=Finset.mem_range.mp hj; omega
      calc
        n.choose j≤ n ^ j:=Nat.choose_le_pow n j
        _≤ (n + 1) ^ r:=by gcongr <;> omega
    _=_:=by simp

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

theorem catalog_bound (n r:ℕ):(catalog n r).length≤ (r + 3) * (n + 1) ^ (r + 2):=by
  have hsub:=List.dedup_sublist (candidates n (r + 2))
  have h:=hsub.length_le.trans (Lax263307Proofs.RationalConditioning.candidate_bound n (r + 2))
  simpa only [catalog,List.length_map,List.length_attach,sets,Nat.add_assoc] using h

theorem catalog_positive (n r:ℕ):0 < (catalog n r).length:=by
  have hmem:=Lax263307Proofs.CoordinateCatalog.catalog_complete n r (⟨∅,by simp⟩:Coordinate n r)
  exact List.length_pos_of_mem hmem

end Lax263307Proofs.CoordinateCatalog

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.ParameterResources

open Lax263307.AlgorithmParameters Lax263307.ParameterResources

theorem logarithm_mono (n:ℕ):Nat.log2 n + 1≤ logarithm n:=by
  unfold logarithm
  rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1

theorem order_bound (n:ℕ) (positive:0 < n):n + 1≤ 2 ^ logarithm n:=by
  have h:=Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * n)
  rw [← Nat.log2_eq_log_two] at h
  exact (show n + 1≤ 2 * n by omega).trans h.le

theorem cutoff_eq_level (a K B n D:ℕ):cutoff a K B n D=level a K B n D:=by
  have h:targetThreshold a K B n D≤ level a K B n D:=by
    unfold level sparsity
    have hfactor:1≤ Nat.log2 n + 1:=by omega
    nlinarith
  exact max_eq_right h

theorem level_bound (a K B n D:ℕ) (positive:0 < D):
    level a K B n D≤
      (2 * K * (12 * B + 1) ^ (4 * a + 2)) * (D * logarithm n) ^ (4 * a + 3):=by
  let X:=D * logarithm n
  have hlog:0 < logarithm n:=by unfold logarithm; omega
  have hX:1≤ X:=Nat.one_le_iff_ne_zero.mpr (by dsimp [X]; positivity)
  have hDX:logarithm n≤ X:=Nat.le_mul_of_pos_left _ positive
  have hLX:Nat.log2 n + 1≤ X:=(logarithm_mono n).trans hDX
  have hload:load B n D + 1≤ (12 * B + 1) * X:=by
    dsimp [load,X]
    nlinarith
  have hpow:=Nat.pow_le_pow_left hload (4 * a + 2)
  have hp:sparsity a K B n D≤ 2 * K * ((12 * B + 1) * X) ^ (4 * a + 2):=by
    unfold sparsity targetThreshold
    simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * K) hpow
  have hlevel:=Nat.mul_le_mul hp hLX
  change level a K B n D≤ _ at hlevel
  change level a K B n D≤ (2 * K * (12 * B + 1) ^ (4 * a + 2)) * X ^ (4 * a + 3)
  calc
    _≤ 2 * K * ((12 * B + 1) * X) ^ (4 * a + 2) * X:=hlevel
    _=_:=by
      rw [mul_pow,show 4 * a + 3=(4 * a + 2) + 1 by omega,pow_succ]
      ring

theorem denominator_eq (a K B n D:ℕ):
    floorDenominator a K B n D=2 * n * level a K B n D:=by
  unfold floorDenominator level
  ring

theorem dimensions_envelope (n r L:ℕ) (order:n + 1≤ 2 ^ L):
    Lax263307.MomentLP.dimension n r≤ 2 ^ (r + 3 + L * (r + 2)):=by
  have hN:=Lax263307Proofs.CoordinateCatalog.catalog_bound n r
  change Lax263307.MomentLP.dimension n r≤ _ at hN
  have hpow:=Nat.pow_le_pow_left order (r + 2)
  have hr:r + 3≤ 2 ^ (r + 3):=Nat.lt_two_pow_self.le
  calc
    _≤ (r + 3) * (n + 1) ^ (r + 2):=hN
    _≤ 2 ^ (r + 3) * (2 ^ L) ^ (r + 2):=Nat.mul_le_mul hr hpow
    _=_:=by rw [← pow_mul, ← pow_add]

theorem resource_bound (a K B:ℕ) (hK:0 < K):
    ∃ C d:ℕ,0 < C∧ 0 < d∧ ∀ n D:ℕ,0 < n→ 0 < D→
      resource a K B n D≤ 2 ^ (C * (D * logarithm n) ^ d):=by
  let c:=2 * K * (12 * B + 1) ^ (4 * a + 2)
  let d:=4 * a + 3
  let A:=c * (c + 2) + 2 * (c + 3) + 20
  let e:=2 * d + 2
  refine ⟨3 * A + 6,e,by positivity,by dsimp [e]; omega, ?_⟩
  intro n D hn hD
  let L:=logarithm n
  let X:=D * L
  let r:=level a K B n D
  let N:=Lax263307.MomentLP.dimension n r
  let Q:=floorDenominator a K B n D
  let M:=radiusDenominator a K B n D
  let U:=2 ^ (A * X ^ e)
  have hLpos:0 < L:=by dsimp [L,logarithm]; omega
  have hXpos:0 < X:=by dsimp [X]; positivity
  have hX1:1≤ X:=hXpos
  have hL:L≤ X:=Nat.le_mul_of_pos_left _ hD
  have hDX:D≤ X:=Nat.le_mul_of_pos_right _ hLpos
  have hd:0 < d:=by dsimp [d]; omega
  have hXd:X≤ X ^ d:=le_self_pow hX1 (by omega)
  have hXdp:1≤ X ^ d:=Nat.one_le_pow _ _ hX1
  have hr:r≤ c * X ^ d:=level_bound a K B n D hD
  have hrpos:0 < r:=by dsimp [r,level,sparsity,targetThreshold]; positivity
  have hQpos:0 < Q:=by
    rw [show Q=2 * n * r from denominator_eq a K B n D]
    positivity
  have hNpos:0 < N:=Lax263307Proofs.CoordinateCatalog.catalog_positive n r
  have hUpos:0 < U:=by dsimp [U]; positivity
  have hU1:1≤ U:=hUpos
  have hnexp:n + 1≤ 2 ^ L:=order_bound n hn
  have hrExp:r≤ 2 ^ (c * X ^ d):=hr.trans Nat.lt_two_pow_self.le
  have hQ:Q≤ 2 ^ ((c + 2) * X ^ d):=by
    calc
      Q=2 * n * r:=denominator_eq a K B n D
      _≤ 2 * 2 ^ L * 2 ^ (c * X ^ d):=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega:n≤ 2 ^ L)) hrExp
      _=2 ^ (1 + L + c * X ^ d):=by
        conv_rhs => rw [pow_add,pow_add]
        norm_num
      _≤ _:=Nat.pow_le_pow_right (by decide) (by nlinarith only [hL.trans hXd,hXdp])
  have hQr:Q ^ r≤ 2 ^ (c * (c + 2) * X ^ (2 * d)):=by
    calc
      _≤ (2 ^ ((c + 2) * X ^ d)) ^ r:=Nat.pow_le_pow_left hQ r
      _=2 ^ (((c + 2) * X ^ d) * r):=(pow_mul 2 ((c + 2) * X ^ d) r).symm
      _≤ _:=by
        apply Nat.pow_le_pow_right (by decide)
        calc
          _≤ ((c + 2) * X ^ d) * (c * X ^ d):=Nat.mul_le_mul_left _ hr
          _=_:=by rw [show 2 * d=d + d by omega,pow_add]; ring
  have hr3:r + 3≤ (c + 3) * X ^ d:=by nlinarith only [hr,hXdp]
  have hN:N≤ 2 ^ (2 * (c + 3) * X ^ (d + 1)):=by
    have hN':=dimensions_envelope n r L hnexp
    apply hN'.trans
    apply Nat.pow_le_pow_right (by decide)
    have hprod:=Nat.mul_le_mul hL (show r + 2≤ (c + 3) * X ^ d by omega)
    calc
      _≤ (c + 3) * X ^ d + X * ((c + 3) * X ^ d):=by omega
      _=((c + 3) * X ^ d) * (1 + X):=by ring
      _≤ ((c + 3) * X ^ d) * (2 * X):=Nat.mul_le_mul_left _ (by omega)
      _=_:=by rw [pow_succ]; ring
  have hn2:n ^ 2≤ 2 ^ (2 * L):=by
    have h:=Nat.pow_le_pow_left (show n≤ 2 ^ L by omega) 2
    simpa only [← pow_mul,Nat.mul_comm L 2] using h
  have hD2:D ^ 2≤ 2 ^ (2 * D):=by
    have h:=Nat.pow_le_pow_left (Nat.lt_two_pow_self.le:D≤ 2 ^ D) 2
    simpa only [← pow_mul,Nat.mul_comm D 2] using h
  have hM:M≤ U:=by
    have hpoly:8 + 2 * (c + 3) * X ^ (d + 1) + 2 * L + 2 * D +
        c * (c + 2) * X ^ (2 * d)≤ A * X ^ e:=by
      have h1e:1≤ X ^ e:=Nat.one_le_pow _ _ hX1
      have hXe:X≤ X ^ e:=le_self_pow hX1 (by dsimp [e]; omega)
      have hp1:=Nat.pow_le_pow_right hX1 (show d + 1≤ e by dsimp [e]; omega)
      have hp2:=Nat.pow_le_pow_right hX1 (show 2 * d≤ e by dsimp [e]; omega)
      have hco1:=Nat.mul_le_mul_left (2 * (c + 3)) hp1
      have hco2:=Nat.mul_le_mul_left (c * (c + 2)) hp2
      have hLe:=hL.trans hXe
      have hDe:=hDX.trans hXe
      dsimp only [A]
      nlinarith only [hco1,hco2,hLe,hDe,h1e]
    calc
      M=256 * N * n ^ 2 * D ^ 2 * Q ^ r:=rfl
      _≤ 256 * 2 ^ (2 * (c + 3) * X ^ (d + 1)) * 2 ^ (2 * L) * 2 ^ (2 * D) *
          2 ^ (c * (c + 2) * X ^ (2 * d)):=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 256 hN) hn2) hD2) hQr
      _=2 ^ (8 + 2 * (c + 3) * X ^ (d + 1) + 2 * L + 2 * D + c * (c + 2) * X ^ (2 * d)):=by
        rw [show (256:ℕ)=2 ^ 8 by decide]
        repeat rw [← pow_add]
      _≤ U:=Nat.pow_le_pow_right (by decide) hpoly
  have hQpow:Q≤ Q ^ r:=le_self_pow (by omega) (by omega)
  have hPowM:Q ^ r≤ M:=
    Nat.le_mul_of_pos_left _ (by dsimp [N]; positivity:0 < 256 * N * n ^ 2 * D ^ 2)
  have hnM:n≤ M:=(show n≤ Q by rw [show Q=2 * n * r from denominator_eq a K B n D]; nlinarith only [hrpos,hn]).trans
    (hQpow.trans hPowM)
  have hrM:r≤ M:=(show r≤ Q by rw [show Q=2 * n * r from denominator_eq a K B n D]; nlinarith only [hrpos,hn]).trans
    (hQpow.trans hPowM)
  have hNM:N≤ M:=by
    have hrest:0 < 256 * n ^ 2 * D ^ 2 * Q ^ r:=by positivity
    have h:=Nat.le_mul_of_pos_right N hrest
    convert h using 1; first | rfl | (dsimp [M,radiusDenominator,N,Q,r]; ring)
  have hDM:D≤ M:=by
    have hrest:0 < 256 * N * n ^ 2 * Q ^ r:=by positivity
    have hDsq:D≤ D ^ 2:=by simpa only [pow_two] using Nat.le_mul_self D
    have h:=hDsq.trans (Nat.le_mul_of_pos_right (D ^ 2) hrest)
    convert h using 1 <;> first | rfl | (dsimp [M,radiusDenominator,N,Q,r]; ring)
  have hpR:sparsity a K B n D≤ r:=Nat.le_mul_of_pos_right _ (by omega)
  have hloadR:load B n D≤ r:=by
    have hpow:load B n D + 1≤ (load B n D + 1) ^ (4 * a + 2):=
      le_self_pow (by omega) (by omega)
    have hcoeff:(load B n D + 1) ^ (4 * a + 2)≤ sparsity a K B n D:=by
      unfold sparsity targetThreshold
      simpa only [mul_assoc] using Nat.le_mul_of_pos_left ((load B n D + 1) ^ (4 * a + 2))
        (by positivity:0 < 2 * K)
    exact (show load B n D≤ load B n D + 1 by omega).trans (hpow.trans (hcoeff.trans hpR))
  have hprec:precision a K B n D≤ 3 * U:=by change M + 2≤ _; omega
  have hiter:iterations a K B n D≤ 32 * U ^ 3:=by
    have hnu:N≤ U:=hNM.trans hM
    have hp:=Nat.mul_le_mul hprec hnu
    have hleft:N + 1≤ 2 * U:=by omega
    have hright:precision a K B n D * N + 1≤ 4 * U ^ 2:=by
      have hUsq:1≤ U ^ 2:=Nat.one_le_pow 2 U hUpos
      nlinarith only [hp,hUsq]
    have h:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 hleft) hright
    change iterations a K B n D≤ _ at h
    convert h using 1; ring
  have hbrute:(n + 1) ^ cutoff a K B n D≤ U:=by
    rw [cutoff_eq_level]
    have h:=Nat.pow_le_pow_left hnexp r
    rw [← pow_mul] at h
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    have hp:=Nat.mul_le_mul hL hr
    have he:X * (c * X ^ d)=c * X ^ (d + 1):=by rw [pow_succ]; ring
    rw [he] at hp
    have hde:=Nat.pow_le_pow_right hX1 (show d + 1≤ e by dsimp [e]; omega)
    have hcA:c≤ A:=by dsimp [A]; nlinarith only [Nat.zero_le c]
    exact hp.trans (Nat.mul_le_mul hcA hde)
  have hsmall:resource a K B n D≤ 64 * U ^ 3:=by
    have hnU:=hnM.trans hM
    have hDU:=hDM.trans hM
    have hloadU:=hloadR.trans (hrM.trans hM)
    have hpU:=hpR.trans (hrM.trans hM)
    have hrU:=hrM.trans hM
    have hNU:=hNM.trans hM
    have hU3:U≤ U ^ 3:=le_self_pow hU1 (by decide)
    dsimp only [resource]
    change n + D + load B n D + sparsity a K B n D + r + N + M +
      precision a K B n D + iterations a K B n D + (n + 1) ^ cutoff a K B n D≤ _
    nlinarith only [hnU,hDU,hloadU,hpU,hrU,hNU,hM,hprec,hiter,hbrute,hU3]
  calc
    resource a K B n D≤ 64 * U ^ 3:=hsmall
    _=2 ^ (6 + 3 * A * X ^ e):=by
      dsimp [U]
      rw [show (64:ℕ)=2 ^ 6 by decide, ← pow_mul, ← pow_add]
      congr 1
      ring
    _≤ 2 ^ ((3 * A + 6) * X ^ e):=by
      apply Nat.pow_le_pow_right (by decide)
      have hXe1:1≤ X ^ e:=Nat.one_le_pow _ _ hX1
      nlinarith only [hXe1]

end Lax263307Proofs.ParameterResources

end

section

namespace Lax263307Proofs.NativeRootResource

open Lax263307 AlgorithmParameters

theorem logarithm_mono {m n:ℕ} (h:m≤ n):logarithm m≤ logarithm n:=by
  unfold logarithm
  rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left 2 h)) 1

theorem envelope_mono (C d D:ℕ) {m n:ℕ} (h:m≤ n):envelope C d m D≤ envelope C d n D:=by
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.mul_le_mul_left D (logarithm_mono h)) d)

theorem uniform (a K b:ℕ) (hK:0< K):
    ∃ C d:ℕ,0< C∧ 0< d∧ ∀ n D m:ℕ,0< D→ 0< m→ m≤ n→
      Lax263307.ParameterResources.resource a K b m D≤ envelope C d n D:=by
  obtain ⟨C,d,hC,hd,hbound⟩:=Lax263307Proofs.ParameterResources.resource_bound a K b hK
  exact ⟨C,d,hC,hd,fun n D m hD hm hmn => (hbound m D hm hD).trans (envelope_mono C d D hmn)⟩

end Lax263307Proofs.NativeRootResource

end

theorem solution:∀ (a K b:Nat),
  Nat.lt ((0:Nat)) K→
    ∃ (C:Nat) (d:Nat),
      And (Nat.lt ((0:Nat)) C)
        (And (Nat.lt ((0:Nat)) d)
          (∀ (n D m:Nat),
            Nat.lt ((0:Nat)) D→
              Nat.lt ((0:Nat)) m→
                Nat.le m n→
                  Nat.le (Lax263307.ParameterResources.resource a K b m D)
                    (Lax263307Proofs.NativeRootResource.envelope C d n D))):= @Lax263307Proofs.NativeRootResource.uniform

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phi_log
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:43:08.32998+00:00
-- url     : https://prove2.me/submissions/e69e88d5-e765-464e-8199-f85edf177ed2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}

open GroundTheory.PAdicHodge.ACris in
theorem solution (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) :
    phi K p (log hx) = log hφ := by
  have hθ0 (y : ACrisZero K p) :
      phi K p (algebraMap (ACrisZero K p) (ACris K p) y) =
        algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y) := by
    rw [show phi K p = AdicCompletion.extendRingHom
        (Ideal.span {(p : ACrisZero K p)}) (Ideal.span {(p : ACris K p)})
        ((algebraMap (ACrisZero K p) (ACris K p)).comp (phiZero K p))
        span_p_le_comap_phiZero from rfl]
    rw [IsHausdorff.eq_iff_smodEq
      (I := (Ideal.span {(p : ACris K p)} : Ideal (ACris K p)))]
    simp only [smul_eq_mul, Ideal.mul_top]
    intro k
    change Ideal.Quotient.mk (Ideal.span {(p : ACris K p)} ^ k) _ =
      Ideal.Quotient.mk (Ideal.span {(p : ACris K p)} ^ k) _
    rw [AdicCompletion.extendRingHom, IsAdicComplete.mk_liftRingHom]
    simp only [AdicCompletion.extendFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    have heval (z : ACrisZero K p) :
        (AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) k)
          (algebraMap (ACrisZero K p) (ACris K p) z) =
        Ideal.Quotient.mk _ z := by
      rw [AlgHom.commutes]
      rfl
    rw [heval, Ideal.quotientMap_mk, RingHom.comp_apply]
  have hterm (n : ℕ) : phi K p (logTerm hx n) = logTerm hφ n := by
    rw [logTerm, logTerm, hθ0]
    congr 1
    refine Subtype.ext ?_
    change (phiAway K p) (logTermZero hx n : 𝔸) = (logTermZero hφ n : 𝔸)
    simp only [logTermZero, dpowZero, Subalgebra.coe_mul, Subalgebra.coe_pow,
      Subalgebra.coe_neg, map_mul, map_pow, map_neg]
    rw [phiAway_dpow]
    simp [map_one, map_natCast]
  have hs : IsAdicSum 𝔭 (logTerm hx) (log hx) := (exists_isAdicSum_logTerm hx).choose_spec
  have hsφ : IsAdicSum 𝔭 (logTerm hφ) (log hφ) := (exists_isAdicSum_logTerm hφ).choose_spec
  have hf : 𝔭 ≤ Ideal.comap (phi K p) 𝔭 := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have hmap : IsAdicSum 𝔭 (fun n => phi K p (logTerm hx n)) (phi K p (log hx)) :=
    IsAdicSum.map (phi K p) hf hs
  have hmap' : IsAdicSum 𝔭 (logTerm hφ) (phi K p (log hx)) := by
    convert hmap using 1
    exact funext fun n => (hterm n).symm
  rw [IsHausdorff.eq_iff_smodEq (I := (𝔭 : Ideal (ACris K p)))]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro k
  obtain ⟨N₁, h₁⟩ := hmap' k
  obtain ⟨N₂, h₂⟩ := hsφ k
  let N := max N₁ N₂
  have a := h₁ N (le_max_left _ _)
  have b := h₂ N (le_max_right _ _)
  refine SModEq.sub_mem.2 ?_
  have hsub : phi K p (log hx) - log hφ =
      (phi K p (log hx) - ∑ n ∈ Finset.range N, logTerm hφ n) -
        (log hφ - ∑ n ∈ Finset.range N, logTerm hφ n) := by
    abel
  rw [hsub]
  exact sub_mem a b

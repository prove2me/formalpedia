-- Prove2me | solution 1 for MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a7412a07-9cfc-5a32-89f5-3d15e1181bb8

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical

set_option autoImplicit false

open MvPowerSeries

universe u v w

namespace MvFormalGroup
p2m_export "MvFormalGroup" "map adicEval"
namespace AdicEvalUnique
p2m_open "MvFormalGroup"

private theorem mem_span_X_pow {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (N : ℕ)
    (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf

    let f₀ : MvPowerSeries σ R := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ R) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have hsub : ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) ⊆
        ((fun s => (X s : MvPowerSeries σ R) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) := by
      apply Set.image_mono
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _
    obtain ⟨g, hg⟩ := h1
    have hfg : f = f₀ + X s₀ ^ N * g := by rw [← hg, add_sub_cancel]
    rw [hfg]
    refine add_mem (Ideal.span_mono hsub h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
    exact ⟨s₀, by rw [Finset.coe_insert]; exact Set.mem_insert _ _, rfl⟩

end MvFormalGroup.AdicEvalUnique

open MvFormalGroup.AdicEvalUnique MvPowerSeries.WithPiTopology in
theorem solution
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S]
    {σ : Type w} [Finite σ] (ψ : MvPowerSeries σ R →ₐ[R] S)
    (hψ : ∀ s, ψ (X s) ∈ J.radical) (f : MvPowerSeries σ R) :
    ψ f = MvFormalGroup.adicEval J (fun s => ψ (X s)) f := by
  classical
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI := Fintype.ofFinite σ

  have hcont : Continuous ψ := by
    apply continuous_of_continuousAt_zero ψ
    rw [ContinuousAt, map_zero, (J.hasBasis_nhds_zero_adic).tendsto_right_iff]
    intro n _

    choose k hk using fun s => (hψ s)
    let K : ℕ := Finset.univ.sup k
    have hkK : ∀ s, k s ≤ K := fun s => Finset.le_sup (Finset.mem_univ s)
    let N : ℕ := n * K

    let d : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
    have hd : ∀ s, d s = N := fun s => rfl
    have hU : {f : MvPowerSeries σ R | ∀ e ∈ Finset.Iic d, coeff e f = 0} ∈
        nhds (0 : MvPowerSeries σ R) := by
      have : {f : MvPowerSeries σ R | ∀ e ∈ Finset.Iic d, coeff e f = 0} =
          ⋂ e ∈ Finset.Iic d, {f : MvPowerSeries σ R | coeff e f = 0} := by
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this, Filter.biInter_finset_mem]
      intro e _
      refine IsOpen.mem_nhds ?_ (by simp [coeff_zero])
      exact (isOpen_discrete ({0} : Set R)).preimage (continuous_coeff (R := R) e)
    filter_upwards [hU] with f hf

    have hmem : f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ (N + 1)) ''
        ((Finset.univ : Finset σ) : Set σ)) := by
      refine mem_span_X_pow (N + 1) Finset.univ f fun e he => hf e ?_
      rw [Finset.mem_Iic, Finsupp.le_def]
      intro s
      rw [hd]
      exact Nat.lt_succ_iff.1 (he s (Finset.mem_univ s))

    have hle : Ideal.map ψ (Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ (N + 1)) ''
        ((Finset.univ : Finset σ) : Set σ))) ≤ J ^ n := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
      change ψ ((X s : MvPowerSeries σ R) ^ (N + 1)) ∈ J ^ n
      rw [map_pow]
      have hNk : n * k s ≤ N + 1 := (Nat.mul_le_mul_left n (hkK s)).trans (Nat.le_succ _)
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hNk
      rw [hr, pow_add, mul_comm n, pow_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hk s) n)
    exact hle (Ideal.mem_map_of_mem _ hmem)

  have h1 := MvPowerSeries.aeval_unique hcont
  calc ψ f = MvPowerSeries.aeval (MvPowerSeries.HasEval.X.map hcont) f := by rw [h1]
    _ = MvPowerSeries.eval₂ (algebraMap R S) (fun s => ψ (X s)) f := by
        rw [MvPowerSeries.coe_aeval]; rfl
    _ = MvFormalGroup.adicEval J (fun s => ψ (X s)) f := rfl

end S_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
end P2MW
export P2MW.S_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (solution)

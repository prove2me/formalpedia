-- Prove2me | solution 1 for LocalNewvector.exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a38b2044-0a2b-56ae-afc9-1abef7c66c2e

import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule

set_option autoImplicit false

namespace SolCFurniture

open Matrix

variable (q : ℕ) [Fact q.Prime]

theorem glMap_padicInt_injective :
    Function.Injective (GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])) := by
  apply Units.map_injective
  intro A B hAB
  ext i j
  have hf : Function.Injective (algebraMap ℤ_[q] ℚ_[q]) := IsFractionRing.injective ℤ_[q] ℚ_[q]
  apply hf
  have := congrArg (fun M => M i j) hAB
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe] using this

variable (a : ℕ)

noncomputable def liftK1Fun (k : LocalNewvector.padicK1 q a) : GL (Fin 2) ℤ_[q] :=
  k.2.choose

theorem glMap_liftK1Fun (k : LocalNewvector.padicK1 q a) :
    GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) (liftK1Fun q a k) = k.1 :=
  (k.2.choose_spec).1

@[simps]
noncomputable def liftK1 : ↥(LocalNewvector.padicK1 q a) →* GL (Fin 2) ℤ_[q] where
  toFun := liftK1Fun q a
  map_one' := by
    apply glMap_padicInt_injective q
    rw [glMap_liftK1Fun, map_one]
    rfl
  map_mul' := by
    intro k₁ k₂
    apply glMap_padicInt_injective q
    rw [map_mul, glMap_liftK1Fun, glMap_liftK1Fun, glMap_liftK1Fun]
    rfl

noncomputable def reductionHom (m : ℕ) :
    ↥(LocalNewvector.padicK1 q a) →* GL (Fin 2) (ZMod (q ^ m)) :=
  (GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZModPow m)).comp (liftK1 q a)

theorem entry_norm_le_of_mem_ker_reductionHom (m : ℕ) (k : LocalNewvector.padicK1 q a)
    (hk : k ∈ (reductionHom q a m).ker) (i j : Fin 2) :
    ‖((k.1 : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j‖ ≤ (q : ℝ) ^ (-(m : ℤ)) := by

  have hred : GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZModPow m) (liftK1Fun q a k) = 1 := by
    have hk' : (reductionHom q a m) k = 1 := MonoidHom.mem_ker.mp hk
    simpa [reductionHom, liftK1_apply, MonoidHom.comp_apply] using hk'

  have hentry : (PadicInt.toZModPow m) ((liftK1Fun q a k : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j := by
    have h := congrArg
      (fun g : GL (Fin 2) (ZMod (q ^ m)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j) hred
    simpa [GeneralLinearGroup.map_apply] using h

  have hk1 : (((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j
      = (((liftK1Fun q a k : Matrix (Fin 2) (Fin 2) ℤ_[q]) - 1) i j : ℚ_[q]) := by
    rw [← glMap_liftK1Fun q a k]
    simp only [GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, Matrix.sub_apply,
      Matrix.one_apply, apply_ite ((↑·) : ℤ_[q] → ℚ_[q]), PadicInt.coe_one, PadicInt.coe_zero,
      PadicInt.coe_sub]
  rw [hk1, ← PadicInt.norm_def, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, Matrix.sub_apply, map_sub, hentry]
  simp only [Matrix.one_apply, apply_ite (PadicInt.toZModPow (p := q) m), map_one, map_zero,
    sub_self]

theorem finiteIndex_gl2CongruenceSubgroup_subgroupOf_padicK1 (m a : ℕ) :
    ((FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf
      (LocalNewvector.padicK1 q a)).FiniteIndex := by

  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (Nat.Prime.ne_zero Fact.out)⟩
  haveI : Finite (reductionHom q a m).range := Subtype.finite
  haveI hker : (reductionHom q a m).ker.FiniteIndex := Subgroup.finiteIndex_ker _

  refine Subgroup.finiteIndex_of_le (H := (reductionHom q a m).ker) ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf, FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  refine ⟨entry_norm_le_of_mem_ker_reductionHom q a m k hk, ?_⟩

  have hkinv : k⁻¹ ∈ (reductionHom q a m).ker := (reductionHom q a m).ker.inv_mem hk
  have := entry_norm_le_of_mem_ker_reductionHom q a m k⁻¹ hkinv
  simpa using this

end SolCFurniture

namespace SolCAux

theorem smul_sum_out_smul {G : Type} [Group G] {V : Type} [AddCommGroup V] [DistribMulAction G V]
    (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] {v : V}
    (hHv : ∀ h : K, h ∈ H → (h : G) • v = v) (k : K) :
    (k : G) • (∑ c : K ⧸ H, ((Quotient.out c : K) : G) • v)
      = ∑ c : K ⧸ H, ((Quotient.out c : K) : G) • v := by
  have hterm : ∀ c : K ⧸ H,
      (k : G) • (((Quotient.out c : K) : G) • v) = ((Quotient.out (k • c) : K) : G) • v := by
    intro c
    have hcos : (QuotientGroup.mk (k * Quotient.out c) : K ⧸ H) = QuotientGroup.mk (Quotient.out (k • c)) := by
      rw [QuotientGroup.out_eq']
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [QuotientGroup.eq] at hcos
    have hfix := hHv _ hcos
    calc (k : G) • (((Quotient.out c : K) : G) • v)
        = ((k * Quotient.out c : K) : G) • v := by rw [Subgroup.coe_mul, mul_smul]
      _ = ((k * Quotient.out c : K) : G) • ((((k * Quotient.out c)⁻¹ * Quotient.out (k • c) : K) : G) • v) := by
          rw [hfix]
      _ = ((Quotient.out (k • c) : K) : G) • v := by
          rw [← mul_smul, ← Subgroup.coe_mul, mul_inv_cancel_left]
  rw [Finset.smul_sum]
  simp_rw [hterm]
  exact Fintype.sum_equiv (MulAction.toPerm k) _ _ (fun c => rfl)

end SolCAux

open SolCAux in
open LocalNewvector in
theorem solution
    (q : ℕ) [Fact q.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[q]) V] [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (T : V →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hT : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), T (x • v) = x • T v)
    (W : Submodule ℂ V) (hW : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ w ∈ W, x • w ∈ W)
    (hsmooth : ∀ w ∈ W, ∃ U : Subgroup (GL (Fin 2) ℚ_[q]),
      IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧ ∀ u ∈ U, u • w = w)
    (a : ℕ) {v : V} (hv : v ∈ W)
    (hTv : T v ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.PSCarrier q μ₁ μ₂)) :
    ∃ y ∈ W, y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) V ∧ T y = T v := by
  classical
  obtain ⟨U, hUopen, hUfix⟩ := hsmooth v hv
  obtain ⟨m, hm⟩ := FLT.SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one q
    (hUopen.mem_nhds U.one_mem)
  haveI : ((FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a)).FiniteIndex :=
    SolCFurniture.finiteIndex_gl2CongruenceSubgroup_subgroupOf_padicK1 q m a
  letI : Fintype (LocalNewvector.padicK1 q a ⧸
      (FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a)) :=
    Fintype.ofFinite _
  have hHv : ∀ h : LocalNewvector.padicK1 q a,
      h ∈ (FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a) →
        (h : GL (Fin 2) ℚ_[q]) • v = v :=
    fun h hh => hUfix _ (hm (Subgroup.mem_subgroupOf.mp hh))

  have hcard : ((Fintype.card (LocalNewvector.padicK1 q a ⧸
      (FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a)) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨((Fintype.card (LocalNewvector.padicK1 q a ⧸
      (FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a)) : ℕ) : ℂ)⁻¹ •
        ∑ c : (LocalNewvector.padicK1 q a ⧸
      (FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a)),
          ((Quotient.out c : LocalNewvector.padicK1 q a) : GL (Fin 2) ℚ_[q]) • v, ?_, ?_, ?_⟩
  · exact W.smul_mem _ (Submodule.sum_mem _ fun c _ => hW _ _ hv)
  · rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro g hg
    rw [smul_comm]
    congr 1
    exact smul_sum_out_smul (LocalNewvector.padicK1 q a) _ hHv ⟨g, hg⟩
  · have hc : ∀ c : (LocalNewvector.padicK1 q a ⧸
      (FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf (LocalNewvector.padicK1 q a)),
        T (((Quotient.out c : LocalNewvector.padicK1 q a) : GL (Fin 2) ℚ_[q]) • v) = T v := by
      intro c
      rw [hT]
      exact (LocalNewvector.mem_fixedSubmodule_iff.mp hTv) _ (Quotient.out c : LocalNewvector.padicK1 q a).2
    rw [map_smul, map_sum]
    simp_rw [hc]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard,
      one_smul]

end S_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
end P2MW
export P2MW.S_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule (solution)

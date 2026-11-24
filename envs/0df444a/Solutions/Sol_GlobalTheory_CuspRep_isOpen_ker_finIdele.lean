-- Prove2me | solution 1 for GlobalTheory.CuspRep.isOpen_ker_finIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:23.926977+00:00
-- url     : https://prove2.me/submissions/66b59c16-6eb6-44d4-8cf5-d12998630b51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
import Theorems.Thm_GlobalTheory_CuspRep_eq_one_of_pow_near
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_nsmul_integral_mem_nhds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CuspRep
namespace GlobalTheory.CuspRep
theorem _root_.solution (E : Type) [Field E] [NumberField E] (ψ : (FiniteAdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (hψ : Continuous ψ) : IsOpen {u | ψ u = 1} := by
  have hV : {u | ‖((ψ u : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 E) E)ˣ) := by
    refine (isOpen_lt (((Units.continuous_val.comp hψ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simp
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : FiniteAdeleRing (𝓞 E) E => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : FiniteAdeleRing (𝓞 E) E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : FiniteAdeleRing (𝓞 E) E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  let P : Set (FiniteAdeleRing (𝓞 E) E) :=
    {c | ∃ a : FiniteAdeleRing (𝓞 E) E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧ c = N • a}
  have hP : P ∈ 𝓝 0 := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN
  have hmul : ∀ x y : FiniteAdeleRing (𝓞 E) E, x - 1 ∈ P → y - 1 ∈ P → x * y - 1 ∈ P := by
    rintro x y ⟨a, ha, e⟩ ⟨b, hb, e'⟩
    refine ⟨a + b + N • (a * b), fun v => add_mem (add_mem (ha v) (hb v)) (nsmul_mem (mul_mem (ha v) (hb v)) N), ?_⟩
    rw [eq_add_of_sub_eq e, eq_add_of_sub_eq e']
    simp only [nsmul_eq_mul]; ring
  let H : Submonoid (FiniteAdeleRing (𝓞 E) E)ˣ :=
    { carrier := {u | (u : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P}
      one_mem' := ⟨by simpa using mem_of_mem_nhds hP, by simpa using mem_of_mem_nhds hP⟩
      mul_mem' := fun {x y} hx hy => ⟨hmul _ _ hx.1 hy.1, by rw [mul_inv, Units.val_mul]; exact hmul _ _ hx.2 hy.2⟩ }
  have hH : (H : Set (FiniteAdeleRing (𝓞 E) E)ˣ) ∈ 𝓝 1 := by
    refine Filter.inter_mem ?_ ?_
    · exact (Units.continuous_val.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
    · exact (Units.continuous_coe_inv.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
  have hk : ∀ u ∈ H, ψ u = 1 := by
    intro u hu
    apply Units.ext
    refine eq_one_of_pow_near fun n => ?_
    obtain ⟨⟨a, ha, e⟩, ⟨b, hb, e'⟩⟩ := pow_mem hu n
    have := hTV (a := u ^ n) (hTT ⟨?_, ?_⟩)
    · simpa using this
    · change ((u ^ n : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T1
      rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
    · change MulOpposite.op (((u ^ n)⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T2
      rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2
  exact ψ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hH hk)
end GlobalTheory.CuspRep

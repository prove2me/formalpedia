-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_map_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:39.648112+00:00
-- url     : https://prove2.me/submissions/95a24975-b454-4ae7-9f17-47fd39763344

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub


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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (φ : G ≃* G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f)
    (x : G) :
    avgOver (K.map φ.toMonoidHom) (fun y => f (φ.symm y)) x = avgOver K f (φ.symm x) := by
  classical
  set K' := K.map φ.toMonoidHom
  set ψ : K ≃* K' := φ.subgroupMap K
  set S := (rightStab f).subgroupOf K
  set S' : Subgroup K' := S.map ψ.toMonoidHom
  have hψ : ∀ k : K, ((ψ k : K') : G) = φ k := fun k => rfl
  have hS' : S' ≤ (rightStab fun y => f (φ.symm y)).subgroupOf K' := by
    rintro _ ⟨s, hs, rfl⟩ y
    show f (φ.symm (y * ((ψ s : K') : G))) = f (φ.symm y)
    rw [hψ, map_mul, MulEquiv.symm_apply_apply]
    exact hs _
  let e : K ⧸ S ≃ K' ⧸ S' := Quotient.congr ψ.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      refine ⟨a⁻¹ * b, h, ?_⟩
      simp
    · rintro ⟨c, hc, hc'⟩
      have : c = a⁻¹ * b := by
        apply ψ.injective
        rw [show ψ.toMonoidHom c = ψ c from rfl] at hc'
        rw [hc']
        simp
      rw [← this]
      exact hc)
  have hidx : S'.index = S.index := by
    rw [Subgroup.index, Subgroup.index]
    exact (Nat.card_congr e).symm
  have hS'i : S'.index ≠ 0 := by rw [hidx]; exact hf
  rw [avgOver_eq_avgSub hS' hS'i]
  unfold avgOver avgSub
  rw [hidx, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun q => ?_
  have he : e q = QuotientGroup.mk (ψ (Quotient.out q)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S' (ψ (Quotient.out q))
  rw [hs]
  have hs2 : ((s : K') : G) ∈ rightStab fun y => f (φ.symm y) := hS' s.2
  have hs3 : f (φ.symm (x * ((ψ (Quotient.out q) : K') : G) * ((s : K') : G))) =
      f (φ.symm (x * ((ψ (Quotient.out q) : K') : G))) := hs2 _
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, hs3, hψ, map_mul, MulEquiv.symm_apply_apply]
end GroundTheory.Automorphic.Parabolic

-- Prove2me | solution 1 for ModularCurve.zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/600f64c0-7ba9-542a-bc01-8207a21dccf3

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime

open ModularCurve Finset

namespace P2mS3VertexGen

variable {ι : Type*} [Fintype ι]

def diffVec [DecidableEq ι] (s s₀ : ι) : characterLattice ι :=
  ⟨Pi.single s 1 - Pi.single s₀ 1, by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]⟩

@[scoped simp] theorem coe_diffVec [DecidableEq ι] (s s₀ : ι) :
    (diffVec s s₀ : ι → ℤ) = Pi.single s 1 - Pi.single s₀ 1 := rfl

theorem eq_sum_smul_diffVec [DecidableEq ι] (s₀ : ι) (D : characterLattice ι) :
    D = ∑ s, (D : ι → ℤ) s • diffVec s s₀ := by
  apply Subtype.ext
  have hD : ∑ s, (D : ι → ℤ) s = 0 := mem_characterLattice.mp D.2
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, coe_diffVec, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hD, zero_smul, sub_zero]
  ext x
  simp [Finset.sum_apply, Pi.single_apply]

theorem dual_apply_eq_sum [DecidableEq ι] (s₀ : ι) (φ : Module.Dual ℤ (characterLattice ι))
    (D : characterLattice ι) :
    φ D = ∑ s, (D : ι → ℤ) s * φ (diffVec s s₀) := by
  conv_lhs => rw [eq_sum_smul_diffVec s₀ D]
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul]

theorem exists_forall_dvd_sub (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (v : ι → ℤ) : ∃ c : ℤ, ∀ s, (e s : ℤ) ∣ v s - c := by
  have hI : Pairwise (Function.onFun IsCoprime fun s => Ideal.span ({(e s : ℤ)} : Set ℤ)) := by
    intro s t hst
    show IsCoprime (Ideal.span {(e s : ℤ)}) (Ideal.span {(e t : ℤ)})
    rw [Ideal.isCoprime_span_singleton_iff]
    exact Nat.isCoprime_iff_coprime.mpr (he hst)
  obtain ⟨c, hc⟩ := Ideal.exists_forall_sub_mem_ideal hI v
  refine ⟨c, fun s => ?_⟩
  have h := Ideal.mem_span_singleton.mp (hc s)
  rw [← dvd_neg, neg_sub]
  exact h

abbrev coord (s₀ : ι) : Module.Dual ℤ (characterLattice ι) :=
  (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype

theorem coord_apply (s₀ : ι) (D : characterLattice ι) : coord s₀ D = (D : ι → ℤ) s₀ := rfl

theorem exists_gramMap_eq (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (s₀ : ι) (φ : Module.Dual ℤ (characterLattice ι)) :
    ∃ (k : ℤ) (D : characterLattice ι), gramMap e D = φ - k • ((e s₀ : ℤ) • coord s₀) := by
  classical

  set v : ι → ℤ := fun s => φ (diffVec s s₀) with hv
  obtain ⟨c, hc⟩ := exists_forall_dvd_sub e he v
  choose m hm using hc

  set k : ℤ := ∑ s, m s with hk
  let D₀ : ι → ℤ := fun s => m s - k * (Pi.single s₀ (1 : ℤ) : ι → ℤ) s
  have hD₀ : D₀ ∈ characterLattice ι := by
    rw [mem_characterLattice]
    simp only [D₀, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_pi_single']
    simp [hk]
  refine ⟨k, ⟨D₀, hD₀⟩, ?_⟩
  apply LinearMap.ext
  intro D'
  have hD' : ∑ s, (D' : ι → ℤ) s = 0 := mem_characterLattice.mp D'.2
  rw [gramMap_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    coord_apply, dual_apply_eq_sum s₀ φ D', smul_eq_mul, smul_eq_mul]

  have hvs : ∀ s, φ (diffVec s s₀) = c + (e s : ℤ) * m s := fun s => by
    have := hm s; simp only [hv] at this; linarith
  simp only [hvs, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hD', zero_mul, zero_add]

  simp only [D₀, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ s, (e s : ℤ) * (k * (Pi.single s₀ (1 : ℤ) : ι → ℤ) s * (D' : ι → ℤ) s) =
      k * ((e s₀ : ℤ) * (D' : ι → ℤ) s₀) := by
    rw [Finset.sum_eq_single s₀]
    · simp; ring
    · intro s _ hs; simp [hs]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  rw [h1]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

theorem zmultiples_eq_top (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t)) (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) • coord s₀)) = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro y
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨k, D, hD⟩ := exists_gramMap_eq e he s₀ φ
  have hφ : φ = k • ((e s₀ : ℤ) • coord s₀) + gramMap e D := by rw [hD]; abel
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
  have h0 : (LinearMap.range (gramMap e)).mkQ (gramMap e D) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ D
  rw [hφ, map_add, h0, add_zero]
  simp only [map_zsmul]

end P2mS3VertexGen
p2m_reactivate "P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime.P2mS3VertexGen"

theorem solution
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) = ⊤ :=
  P2mS3VertexGen.zmultiples_eq_top e he s₀

end S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime
end P2MW
export P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime (solution)

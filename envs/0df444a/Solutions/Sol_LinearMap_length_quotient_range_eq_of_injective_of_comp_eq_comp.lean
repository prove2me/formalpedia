-- Prove2me | solution 1 for LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/346dd313-64f3-54bb-9c00-079cb3067ebd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp

set_option autoImplicit false

universe u

namespace LinearMap
p2m_export "LinearMap" "range range_comp det_toMatrix' smul_apply ker_comp pi quotKerEquivRange range_comp_le_range ker toMatrix' exact_subtype_mkQ toMatrix'_mulVec"
namespace LengthQuotientIsogeny
p2m_open "LinearMap"

section General

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

private theorem length_eq_length_submodule_add (N : Submodule A M) :
    Module.length A M = Module.length A ↥N + Module.length A (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
    (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)

private theorem length_quotient_eq_add {P Q : Submodule A M} (h : P ≤ Q) :
    Module.length A (M ⧸ P) =
      Module.length A ↥(Q.map P.mkQ) + Module.length A (M ⧸ Q) := by
  rw [length_eq_length_submodule_add (Q.map P.mkQ),
    (Submodule.quotientQuotientEquivQuotient P Q h).length_eq]

private theorem length_map_mkQ_range (P : Submodule A M) {N' : Type*} [AddCommGroup N']
    [Module A N'] (g : N' →ₗ[A] M) :
    Module.length A ↥((LinearMap.range g).map P.mkQ) =
      Module.length A (N' ⧸ LinearMap.ker (P.mkQ ∘ₗ g)) := by
  rw [← LinearMap.range_comp]
  exact (LinearMap.quotKerEquivRange (P.mkQ ∘ₗ g)).length_eq.symm

end General

section Lattice

variable {A : Type*} [CommRing A] {r : ℕ}

private theorem det_ne_zero_of_injective [IsDomain A] (φ : (Fin r → A) →ₗ[A] (Fin r → A))
    (hφ : Function.Injective φ) : LinearMap.det φ ≠ 0 := by
  classical
  intro hdet
  rw [← LinearMap.det_toMatrix'] at hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [LinearMap.toMatrix'_mulVec] at hv0
  exact hv (hφ (hv0.trans (map_zero φ).symm))

private theorem smul_mem_range (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (m : Fin r → A) :
    LinearMap.det φ • m ∈ LinearMap.range φ := by
  classical
  refine ⟨(LinearMap.toMatrix' φ).adjugate.mulVec m, ?_⟩
  rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec, LinearMap.det_toMatrix']

end Lattice

end LinearMap.LengthQuotientIsogeny

open LinearMap.LengthQuotientIsogeny in
theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {r : ℕ}
    (F₁ F₂ φ : (Fin r → A) →ₗ[A] (Fin r → A))
    (hF₁ : Function.Injective F₁) (hφ : Function.Injective φ)
    (hcomm : φ ∘ₗ F₂ = F₁ ∘ₗ φ) :
    Module.length A ((Fin r → A) ⧸ LinearMap.range F₁) =
      Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by
  classical

  set N : Submodule A (Fin r → A) := LinearMap.range φ with hN
  set P : Submodule A (Fin r → A) := LinearMap.range (F₁ ∘ₗ φ) with hP
  have hP1 : P ≤ LinearMap.range F₁ := LinearMap.range_comp_le_range φ F₁
  have hP2 : P ≤ N := by
    rw [hP, ← hcomm]
    exact LinearMap.range_comp_le_range F₂ φ

  have ha := length_quotient_eq_add hP1
  have hb := length_quotient_eq_add hP2

  have ha' : Module.length A ↥((LinearMap.range F₁).map P.mkQ) =
      Module.length A ((Fin r → A) ⧸ N) := by
    rw [length_map_mkQ_range]
    have hker : LinearMap.ker (P.mkQ ∘ₗ F₁) = N := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, hP, LinearMap.range_comp,
        Submodule.comap_map_eq_of_injective hF₁]
    exact (Submodule.quotEquivOfEq _ _ hker).length_eq

  have hb' : Module.length A ↥(N.map P.mkQ) =
      Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by
    rw [hN, length_map_mkQ_range]
    have hker : LinearMap.ker (P.mkQ ∘ₗ φ) = LinearMap.range F₂ := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, hP, ← hcomm, LinearMap.range_comp,
        Submodule.comap_map_eq_of_injective hφ]
    exact (Submodule.quotEquivOfEq _ _ hker).length_eq

  have hfin : Module.length A ((Fin r → A) ⧸ N) ≠ ⊤ := by
    set d := LinearMap.det φ with hd
    have hd0 : d ≠ 0 := det_ne_zero_of_injective φ hφ
    let D : Submodule A (Fin r → A) :=
      Submodule.pi Set.univ (fun _ : Fin r => (Ideal.span {d} : Submodule A A))
    have hDN : D ≤ N := by
      intro m hm
      rw [Submodule.mem_pi] at hm
      choose a ha using fun i => Ideal.mem_span_singleton'.1 (hm i (Set.mem_univ i))
      have hm' : m = d • a := by
        funext i
        rw [Pi.smul_apply, smul_eq_mul, mul_comm, ha i]
      rw [hm']
      exact smul_mem_range φ a
    have hle : Module.length A ((Fin r → A) ⧸ N) ≤ Module.length A ((Fin r → A) ⧸ D) :=
      Module.length_le_of_surjective (Submodule.factor hDN) (Submodule.factor_surjective hDN)
    have hD : Module.length A ((Fin r → A) ⧸ D) ≠ ⊤ := by
      rw [(Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
      exact WithTop.sum_ne_top.2 fun i _ => Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hd0)
    exact ne_top_of_le_ne_top hD hle

  rw [ha', add_comm] at ha
  rw [hb'] at hb
  exact WithTop.add_right_cancel hfin (ha.symm.trans hb)

end S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp
end P2MW
export P2MW.S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp (solution)

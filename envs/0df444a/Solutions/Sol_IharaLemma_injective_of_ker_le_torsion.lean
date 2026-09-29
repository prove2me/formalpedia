-- Prove2me | solution 1 for IharaLemma.injective_of_ker_le_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1f21211d-497d-50a8-96d0-5510b0e3128a

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_injective_of_ker_le_torsion

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (S : Submonoid R)
    {V W V' W' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
    (g : V →ₗ[R] V') [IsLocalizedModule S g] (h : W →ₗ[R] W') [IsLocalizedModule S h]
    (f : V →ₗ[R] W) (F : V' →ₗ[R] W') (hcomm : ∀ v, F (g v) = h (f v))
    (E : Submodule R V) (hE : ∀ e ∈ E, ∃ s : S, (s : R) • e = 0) (hker : ∀ v, f v = 0 → v ∈ E) :
    Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨v, s⟩, hv⟩ := IsLocalizedModule.surj S g x

  have hv' : (s : R) • x = g v := hv
  have hfv : h (f v) = 0 := by
    rw [← hcomm, ← hv', map_smul, hx, smul_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff S h).mp hfv

  have hc' : (c : R) • f v = 0 := hc
  have hcv : f ((c : R) • v) = 0 := by rw [map_smul]; exact hc'
  obtain ⟨s', hs'⟩ := hE _ (hker _ hcv)

  apply IsLocalizedModule.smul_injective g (s' * c * s)
  show ((s' * c * s : S) : R) • x = ((s' * c * s : S) : R) • 0
  rw [smul_zero, Submonoid.coe_mul, Submonoid.coe_mul, mul_smul, mul_smul]
  rw [hv', ← map_smul, ← map_smul, hs', map_zero]

#print axioms solution

end S_IharaLemma_injective_of_ker_le_torsion
end P2MW
export P2MW.S_IharaLemma_injective_of_ker_le_torsion (solution)

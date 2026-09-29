-- Prove2me | solution 1 for MonoidAlgebra.quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8d8c5f2e-d38a-54fc-a423-5e580f5ae1f9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top

set_option autoImplicit false

theorem solution
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] {G : Type} [CommGroup G] [Fintype G]
    (ι : MonoidAlgebra 𝒪 G →ₐ[𝒪] A) (Mn : Type) [AddCommGroup Mn] [Module A Mn]
    [Module (MonoidAlgebra 𝒪 G) Mn] [Module 𝒪 Mn] [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 G) Mn]
    (hι : ∀ (c : MonoidAlgebra 𝒪 G) (x : Mn), c • x = ι c • x) (x : Mn) :
    (Submodule.Quotient.mk x :
        Mn ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) •
          (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn))) = 0 ↔
      x ∈ (Ideal.map ι (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)))) • (⊤ : Submodule A Mn) := by

  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro c hc m _
      rw [hι]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem ι hc) Submodule.mem_top
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  · intro hx
    have key : ∀ a ∈ Ideal.map ι (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G))), ∀ m : Mn,
        a • m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) •
          (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn)) := by
      intro a ha
      rw [Ideal.map] at ha
      refine Submodule.span_induction
        (p := fun a _ => ∀ m : Mn, a • m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) •
          (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn))) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨c, hc, rfl⟩ m
        rw [← hι]
        exact Submodule.smul_mem_smul hc Submodule.mem_top
      · intro m
        rw [zero_smul]
        exact Submodule.zero_mem _
      · intro a b _ _ ha hb m
        rw [add_smul]
        exact Submodule.add_mem _ (ha m) (hb m)
      · intro s b _ hb m
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact hb (s • m)
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha m _
      exact key a ha m
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb

end S_MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top
end P2MW
export P2MW.S_MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top (solution)

-- Prove2me | solution 1 for Module.length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9a4750f7-9f65-5ae6-bc9c-f1423b5e2579

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin

set_option autoImplicit false

open scoped BigOperators

namespace ColengthInBasisAux

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem main (P : Submodule R M) (e : Fin 2 → M) (he : ∀ r, e r ∈ P)
    (heb : ∀ m ∈ P, ∃! w : Fin 2 → R, m = ∑ r, w r • e r)
    (A : Matrix (Fin 2) (Fin 2) R) :
    Module.length R (↥P ⧸ Submodule.comap P.subtype
        (Submodule.span R (Set.range fun s : Fin 2 => ∑ r, A r s • e r))) =
      Module.length R ((Fin 2 → R) ⧸ LinearMap.range (Matrix.mulVecLin A)) := by
  classical

  let ψ : (Fin 2 → R) →ₗ[R] M := Fintype.linearCombination R e
  have hψ : ∀ w, ψ w = ∑ r, w r • e r := fun w => Fintype.linearCombination_apply R e w
  have hψP : ∀ w, ψ w ∈ P := fun w => by
    rw [hψ]
    exact P.sum_mem fun r _ => P.smul_mem _ (he r)
  let φ₀ : (Fin 2 → R) →ₗ[R] ↥P := LinearMap.codRestrict P ψ hψP
  have hφ₀ : ∀ w, ((φ₀ w : ↥P) : M) = ∑ r, w r • e r := fun w => hψ w
  have hinj : Function.Injective φ₀ := by
    intro w w' h
    have h' : ∑ r, w r • e r = ∑ r, w' r • e r := by
      rw [← hφ₀, ← hφ₀, h]
    obtain ⟨u, -, huniq⟩ := heb _ (hψP w)
    exact ((huniq w (hψ w)).trans (huniq w' ((hψ w).trans h')).symm)
  have hsurj : Function.Surjective φ₀ := by
    rintro ⟨m, hm⟩
    obtain ⟨w, hw, -⟩ := heb m hm
    exact ⟨w, Subtype.ext ((hφ₀ w).trans hw.symm)⟩
  let φ : (Fin 2 → R) ≃ₗ[R] ↥P := LinearEquiv.ofBijective φ₀ ⟨hinj, hsurj⟩
  have hφ : ∀ w, ((φ w : ↥P) : M) = ∑ r, w r • e r := fun w => hφ₀ w

  let colP : Fin 2 → ↥P := fun s => ⟨∑ r, A r s • e r, P.sum_mem fun r _ => P.smul_mem _ (he r)⟩
  have hcol : ∀ s, φ (A.col s) = colP s := fun s => Subtype.ext (by rw [hφ]; rfl)

  have h1 : Submodule.map (φ : (Fin 2 → R) →ₗ[R] ↥P) (LinearMap.range (Matrix.mulVecLin A)) =
      Submodule.span R (Set.range colP) := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    exact congrArg (fun f : Fin 2 → ↥P => Submodule.span R (Set.range f)) (funext hcol)
  have h2 : Submodule.comap P.subtype (Submodule.span R (Set.range fun s : Fin 2 => ∑ r, A r s • e r)) =
      Submodule.span R (Set.range colP) := by
    have : Submodule.span R (Set.range fun s : Fin 2 => ∑ r, A r s • e r) =
        Submodule.map P.subtype (Submodule.span R (Set.range colP)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [this, Submodule.comap_map_eq_of_injective P.injective_subtype]
  exact ((Submodule.Quotient.equiv _ _ φ (h1.trans h2.symm)).length_eq).symm

end ColengthInBasisAux

theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (P : Submodule R M) (e : Fin 2 → M) (he : ∀ r, e r ∈ P)
    (heb : ∀ m ∈ P, ∃! w : Fin 2 → R, m = ∑ r, w r • e r)
    (A : Matrix (Fin 2) (Fin 2) R) :
    Module.length R (↥P ⧸ Submodule.comap P.subtype
        (Submodule.span R (Set.range fun s : Fin 2 => ∑ r, A r s • e r))) =
      Module.length R ((Fin 2 → R) ⧸ LinearMap.range (Matrix.mulVecLin A)) :=
  ColengthInBasisAux.main P e he heb A

end S_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin
end P2MW
export P2MW.S_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin (solution)

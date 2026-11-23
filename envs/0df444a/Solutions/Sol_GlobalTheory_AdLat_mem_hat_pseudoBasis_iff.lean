-- Prove2me | solution 1 for GlobalTheory.AdLat.mem_hat_pseudoBasis_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:23.353008+00:00
-- url     : https://prove2.me/submissions/ff40fa67-1d51-4476-b530-182dfdc9364d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Theorems.Thm_GlobalTheory_AdLat_adCoord_tmul
import Theorems.Thm_GlobalTheory_AdLat_adCoord_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat
namespace _root_.GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) := by
  intro F E _ _ _ _ _ n L e cI hL z
  constructor
  · intro hz b
    rw [← _root_.GlobalTheory.AdLat.adCoord_sum F e z b]
    have key : _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ≤
        (_root_.GlobalTheory.AdLat.hat1 F (cI b : Set E)).comap (_root_.GlobalTheory.AdLat.adCoord F e b) := by
      unfold _root_.GlobalTheory.AdLat.hat
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, x, hx, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      rw [_root_.GlobalTheory.AdLat.adCoord_tmul]
      unfold _root_.GlobalTheory.AdLat.hat1
      exact AddSubgroup.subset_closure ⟨c, hc, _, (hL x).1 hx b, rfl⟩
    exact key hz
  · intro hz
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have key : _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) ≤
        (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))).comap
          ((smulAddHom (_root_.GlobalTheory.AdLat.RA F E)
            (Fin n → _root_.GlobalTheory.AdLat.RA F E)).flip (_root_.GlobalTheory.AdLat.fv F (e a))) := by
      unfold _root_.GlobalTheory.AdLat.hat1
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, y, hy, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      have hmem : y • e a ∈ L := by
        rw [hL]
        intro a'
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; simpa using hy
        · simpa using (cI a').zero_mem
      unfold _root_.GlobalTheory.AdLat.hat
      refine AddSubgroup.subset_closure ⟨c, hc, _, hmem, ?_⟩
      funext i
      unfold _root_.GlobalTheory.AdLat.fv
      change (c ⊗ₜ[F] y) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e a i) = c ⊗ₜ[F] (y • e a) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, smul_eq_mul]
    exact key (hz a)
end _root_.GlobalTheory.AdLat
end GlobalTheory.AdLat

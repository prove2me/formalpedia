-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:31.353143+00:00
-- url     : https://prove2.me/submissions/86ab6994-9a66-4510-9513-fb06220cdb5d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_forall_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
open CategoryTheory Abelian
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) := by
  have hprime : ∀ p : Ideal R, p.IsPrime →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ p)) (n + 1) := by
    intro p
    induction p using WellFoundedGT.induction with
    | _ p ih =>
    intro hp
    by_cases hpm : p = maximalIdeal R
    · subst hpm; exact hk
    · have hlt : p < maximalIdeal R := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) hpm
      obtain ⟨x, hxm, hxp⟩ := Set.exists_of_ssubset hlt
      let N := R ⧸ p
      have hx0 : Ideal.Quotient.mk p x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have reg : IsSMulRegular N x := by
        intro a b h
        simp only [Algebra.smul_def] at h
        exact mul_left_cancel₀ hx0 h
      have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R N) reg
      have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x N)) (n + 1) := by
        refine hasProjectiveDimensionLT_of_forall_prime (n + 1) (p ⊔ span {x}) ?_ _ ?_
        · intro q hq hle
          exact ih q (lt_of_le_of_ne (le_sup_left.trans hle) (fun h ↦ hxp (h ▸
            hle (le_sup_right (a := p) ((span_singleton_le_iff_mem _).mp le_rfl))))) hq
        · intro a ha m
          have hann : p ⊔ span {x} ≤ Module.annihilator R (QuotSMulTop x N) := by
            refine sup_le ?_ ((span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator N x))
            intro b hb
            rw [Module.mem_annihilator]
            intro m
            obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
            obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
            rw [← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
              Ideal.Quotient.eq_zero_iff_mem.mpr (p.mul_mem_right m hb), map_zero]
          exact Module.mem_annihilator.mp (hann ha) m
      apply ModuleCat.hasProjectiveDimensionLT_of_forall_finite
      intro L _
      have zero := HasProjectiveDimensionLT.subsingleton
        (ModuleCat.of R (QuotSMulTop x N)) (n + 1) (n + 2) (by omega) L
      have exac := Ext.contravariant_sequence_exact₁' hS L (n + 1) (n + 2) (add_comm 1 (n + 1))
      have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
      have : (ModuleCat.smulShortComplex (ModuleCat.of R N) x).f = x • 𝟙 (ModuleCat.of R N) := rfl
      simp only [this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
      by_contra! ntr
      have : x ∈ (Module.annihilator R (Ext (ModuleCat.of R N) L (n + 1))).jacobson :=
        (IsLocalRing.maximalIdeal_le_jacobson _) hxm
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases epi y with ⟨z, hz⟩
      simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
        Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
      simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  exact hasProjectiveDimensionLT_of_forall_prime (n + 1) ⊥ (fun q hq _ ↦ hprime q hq) M
    (fun a ha m ↦ by rw [(Submodule.mem_bot R).mp ha, zero_smul])
end GroundTheory.Arith.SchemeCoh

-- Prove2me | solution 1 for GroundTheory.Arith.Jacobian.spanFinrank_quotient_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:31.713903+00:00
-- url     : https://prove2.me/submissions/fcf2946e-ba70-41df-9a88-ef91270a393e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Jacobian
open IsLocalRing TensorProduct
universe u
noncomputable section
variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]
variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))
variable [IsNoetherianRing P]
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S]
include hsurj
namespace GroundTheory.Arith.Jacobian
theorem _root_.solution (J : Ideal P) [IsLocalRing (P ⧸ J)]
    (hcov : RingHom.ker (algebraMap P S) ≤ J ⊔ maximalIdeal P ^ 2) :
    (maximalIdeal (P ⧸ J)).spanFinrank ≤ (maximalIdeal S).spanFinrank := by
  have : IsNoetherianRing S := isNoetherianRing_of_surjective P S _ hsurj
  obtain ⟨G, hGc, hGs⟩ :=
    Submodule.FG.exists_span_set_encard_eq_spanFinrank (Ideal.fg_of_isNoetherianRing (maximalIdeal S))
  have hGfin : G.Finite := Set.finite_of_encard_eq_coe hGc
  set σ := Function.surjInv hsurj
  have hσ : ∀ s, algebraMap P S (σ s) = s := Function.surjInv_eq hsurj
  have hcomap : (maximalIdeal (P ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal P :=
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmap : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal P) ≤ maximalIdeal (P ⧸ J) :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hσm : ∀ g ∈ G, σ g ∈ maximalIdeal P := by
    intro g hg
    rw [← comap_maximalIdeal_eq hsurj, Ideal.mem_comap, hσ, ← hGs]
    exact Submodule.subset_span hg
  have hnsub : maximalIdeal P ≤ Ideal.span (σ '' G) ⊔ RingHom.ker (algebraMap P S) := by
    intro x hx
    have hx' : algebraMap P S x ∈ Ideal.map (algebraMap P S) (Ideal.span (σ '' G)) := by
      rw [Ideal.map_span, Set.image_image]
      have : (fun g => algebraMap P S (σ g)) '' G = G := by
        simp only [hσ, Set.image_id']
      rw [this]
      change algebraMap P S x ∈ Submodule.span S G
      rw [hGs, ← Ideal.mem_comap, comap_maximalIdeal_eq hsurj]
      exact hx
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hx'
    refine Submodule.mem_sup.2 ⟨y, hy, x - y, ?_, by ring⟩
    rw [RingHom.mem_ker, map_sub, hyx, sub_self]
  set T : Set (P ⧸ J) := Ideal.Quotient.mk J '' (σ '' G)
  have hTm : T ⊆ maximalIdeal (P ⧸ J) := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact hmap (Ideal.mem_map_of_mem _ (hσm g hg))
  have hle : maximalIdeal (P ⧸ J) ≤ Ideal.span T := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson ⊥)
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx : x ∈ maximalIdeal P := by rw [← hcomap]; exact hz
    have hx2 : x ∈ Ideal.span (σ '' G) ⊔ (J ⊔ maximalIdeal P ^ 2) :=
      sup_le_sup_left hcov _ (hnsub hx)
    have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hx2
    rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_pow] at h3
    have H : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal P) ^ 2 ≤
        maximalIdeal (P ⧸ J) • maximalIdeal (P ⧸ J) := by
      rw [pow_two, Ideal.smul_eq_mul]
      exact Ideal.mul_mono hmap hmap
    exact sup_le_sup_left H _ h3
  have heq : maximalIdeal (P ⧸ J) = Ideal.span T :=
    le_antisymm hle (Ideal.span_le.2 hTm)
  rw [heq]
  calc (Ideal.span T).spanFinrank ≤ T.ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite ((hGfin.image _).image _)
    _ ≤ (σ '' G).ncard := Set.ncard_image_le (hGfin.image _)
    _ ≤ G.ncard := Set.ncard_image_le hGfin
    _ = (maximalIdeal S).spanFinrank := by rw [Set.ncard_def, hGc, ENat.toNat_natCast]
end GroundTheory.Arith.Jacobian

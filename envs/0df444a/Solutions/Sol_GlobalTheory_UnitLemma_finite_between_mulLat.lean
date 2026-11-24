-- Prove2me | solution 1 for GlobalTheory.UnitLemma.finite_between_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:37.834069+00:00
-- url     : https://prove2.me/submissions/881d01dd-d581-4a5c-99f4-eb83f398dac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLattice
import Theorems.Thm_GlobalTheory_UnitLemma_finite_quot_span_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (c : K.O) (hc : c ≠ 0) :
    {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  haveI := finite_quot_span_of_ne_zero K.O c hc
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  have hfg : (⊤ : Submodule K.O L).FG := Module.Finite.fg_top
  set S : Submodule K.O L := Ideal.span {c} • (⊤ : Submodule K.O L) with hS
  haveI : Finite (L ⧸ S) := Submodule.finite_quotient_smul _ hfg
  haveI : Finite (Submodule K.O (L ⧸ S)) :=
    Finite.of_injective (fun P : Submodule K.O (L ⧸ S) => (P : Set (L ⧸ S))) SetLike.coe_injective
  let f : Submodule K.O B.A → Submodule K.O (L ⧸ S) := fun M => (M.comap L.subtype).map S.mkQ
  have hSle : ∀ M : Submodule K.O B.A, mulLat K.O (algebraMap K.O B.A c) L ≤ M → S ≤ M.comap L.subtype := by
    intro M hM
    rw [hS, Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx : algebraMap K.O B.A c * (x : B.A) ∈ M := hM ⟨x, x.2, rfl⟩
    have : ((a * c) • x : L) = (a • (algebraMap K.O B.A c * (x : B.A)) : B.A) := by
      rw [Submodule.coe_smul, ← Algebra.smul_def, smul_smul]
    rw [Submodule.mem_comap, Submodule.subtype_apply, this]
    exact M.smul_mem a hx
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M₁ h₁ M₂ h₂ heq
  have e1 : M₁.comap L.subtype = M₂.comap L.subtype := by
    have := congrArg (Submodule.comap S.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.2 (hSle M₁ h₁.1), sup_eq_right.2 (hSle M₂ h₂.1)] at this
  have e2 := congrArg (Submodule.map L.subtype) e1
  rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 h₁.2,
    inf_eq_right.2 h₂.2] at e2
end GlobalTheory.UnitLemma

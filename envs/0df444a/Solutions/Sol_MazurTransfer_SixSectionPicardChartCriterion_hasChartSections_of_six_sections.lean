-- Prove2me | solution 1 for MazurTransfer.SixSectionPicardChartCriterion.hasChartSections_of_six_sections
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:30:43.90798+00:00
-- url     : https://prove2.me/submissions/612883bf-ec91-46b7-a155-30229910df7d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted the complete section-selection argument from official Anthropic FLT
exists_finite_etale_hasChartSections_of_field at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2. Original attribution retained.
Design boundary: six fibrewise distinct sections and genus-two geometric
Riemann-Roch models give original HasChartSections, with all triples indexed.
Named downstream consumer: the six actual marked order-13 integral sections.
Their distinctness and geometric model inputs remain explicit obligations.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_MazurTransfer_SixSectionTripleFamilyPublic
import Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra
open MazurTransfer.SixSectionPicardChartCriterion
theorem solution {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (σ : Fin 6 → SchemeHomOver (𝟙 (Spec (.of R))) c)
    (hσ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (.of k) ⟶ Spec (.of R)),
      Function.Injective (fun i => s ≫ (σ i).1))
    (hmodel : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (.of k) ⟶ Spec (.of R)),
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L)
        (M : CurveModel k L) (e : M.C ≅ pullback c s)
        (he : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L),
        ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2) :
    HasChartSections c (g := 2) (r := 5) (tripleFamily c σ) := by
  classical
  intro k _ _ s
  obtain ⟨L, _, _, _, M, e, he, Kc, hRR⟩ := hmodel k s
  refine ⟨L, inferInstance, inferInstance, M, e, he, ⟨Kc,hRR⟩, ?_⟩
  intro D _ hdegD
  let P : {p : Spec (.of k) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _} → Place k L :=
    fun q => M.pointEquivPlace ⟨q.1 ≫ e.inv, by
      rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact q.2⟩
  have hPinj : Function.Injective P := by
    intro q q' h
    have h1 := congrArg Subtype.val (M.pointEquivPlace.injective h)
    exact Subtype.ext ((cancel_mono e.inv).mp h1)
  let pl : Fin 6 → Place k L := fun i => P (sectionFibrePoint (σ i) s)
  have key : ∀ i, (sectionFibrePoint (σ i) s).1 ≫ pullback.fst c s = s ≫ (σ i).1 :=
    fun _ => pullback.lift_fst _ _ _
  have hplinj : Function.Injective pl := by
    intro i j h
    have h1 := congrArg (fun q => q.1 ≫ pullback.fst c s) (hPinj h)
    rw [key,key] at h1
    exact hσ k s h1
  let S : Finset (Place k L) := Finset.univ.image pl
  have hScard : 5+1 ≤ S.card := by
    rw [Finset.card_image_of_injective _ hplinj, Finset.card_univ, Fintype.card_fin]
  have hS1 : ∀ v ∈ S, v.deg = 1 := fun v _ => IsCurveOver.deg_eq_one_of_isAlgClosed v
  obtain ⟨f, _, hfS, hf⟩ :=
    AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
      (g := 2) (r := 5) hRR (by omega) S hS1 hScard D hdegD
  have hch : ∀ j, ∃ i, pl i = f j := fun j => by
    simpa [S, Finset.mem_image] using hfS j
  choose μ hμ using hch
  refine ⟨(Fintype.equivFin (Fin 3 → Fin 6)) μ, ?_⟩
  change ell (D - ∑ j, Finsupp.single
    (P (sectionFibrePoint (σ ((Fintype.equivFin (Fin 3 → Fin 6)).symm
      ((Fintype.equivFin (Fin 3 → Fin 6)) μ) j)) s)) 1) = 1
  simp only [Equiv.symm_apply_apply]
  have hsum : ∑ j, Finsupp.single (P (sectionFibrePoint (σ (μ j)) s)) (1 : ℤ) =
      ∑ j, Finsupp.single (f j) 1 :=
    Finset.sum_congr rfl fun j _ => by rw [← hμ j]
  rw [hsum]
  exact hf
#print axioms solution

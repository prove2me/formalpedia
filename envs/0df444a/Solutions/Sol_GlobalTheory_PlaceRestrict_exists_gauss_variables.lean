-- Prove2me | solution 1 for GlobalTheory.PlaceRestrict.exists_gauss_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:47.071638+00:00
-- url     : https://prove2.me/submissions/ec3208a9-33f1-489b-b8a9-414011fe2514

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_indep_u
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_ratio_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_residueTrdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PlaceRestrict
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace GlobalTheory.PlaceRestrict
theorem _root_.solution (d : Data K ι Ω WT A) (hd : d.AxH 𝒜)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) (j0 : Fin (d.N + 1))
    (hw0 : d.w j0 c ≠ 0) :
    ∃ t : SVar d.D d.N → OmS (Ω c) d.D d.N,
      (∀ P : MvPolynomial (SVar d.D d.N) (Ω c), ∃ Q : MvPolynomial (SVar d.D d.N) (Ω c),
        MvPolynomial.aeval t Q = algebraMap _ (OmS (Ω c) d.D d.N) P) ∧
      ∀ w ∈ d.PlOver la c, (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) →
        ∃ ht : ∀ s, t s ∈ vRing w,
          letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          AlgebraicIndependent
            (ResidueField ((vRing w).comap (algebraMap (Ω c) (OmS (Ω c) d.D d.N))))
            (fun s => residue (vRing w) ⟨t s, ht s⟩) := by
  classical

  have hex : ∀ j, ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    intro j
    have hb := hd.w_base c
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL)
      (fun h0 => hb (congrArg Subtype.val h0))).mp (hd.finrank_one c d.wL) ⟨d.w j c, hd.w_mem j c⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  let a : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)
  have ha : ∀ j, d.w j c = a j • d.w (d.jc c) c := fun j => by
    obtain ⟨b, hb⟩ := hex j
    rw [show a j = b from ratio_eq (hd.w_base c) hb]
    exact hb
  have ha_jc : a (d.jc c) = 1 := ratio_eq (hd.w_base c) (one_smul _ _).symm
  let f := algebraMap (Ω c) (OmS (Ω c) d.D d.N)
  have ha0 : a j0 ≠ 0 := by
    intro h0
    apply hw0
    rw [ha j0, h0, zero_smul]
  have hf0 : f (a j0) ≠ 0 := (map_ne_zero f).mpr ha0
  let r : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c)
  have hr : ∀ j, r j * a j0 = a j := fun j => by
    have : r j = a j / a j0 :=
      ratio_eq hw0 (by rw [ha j, ha j0, smul_smul, div_mul_cancel₀ _ ha0])
    rw [this, div_mul_cancel₀ _ ha0]
  have hr0 : r j0 = 1 := ratio_eq hw0 (one_smul _ _).symm

  let s : TVar d.D d.N → OmS (Ω c) d.D d.N := sImg (D := d.D) (d.jc c) (d.x c)
  have hOT : ∀ p, d.OTtoS c (MvPolynomial.X p) = s p := by
    intro p; simp [Data.OTtoS, OTtoKT, Data.sH, sHom, s]
  have hC : ∀ y : Ω c, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (MvPolynomial.C y) = f y := fun y =>
    (IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) _ y).symm
  have hrel : ∀ i : Fin (d.D + 1), i ≠ 0 → ∑ j, s (i, j) * f (a j) = 0 := by
    intro i hi
    rw [Fin.sum_univ_succAbove _ (d.jc c)]
    simp only [s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, hi, ↓reduceIte, ha_jc, map_one, mul_one, map_neg, map_sum,
      map_mul, hC]
    rw [neg_add_eq_zero]
    rfl
  have hrel0 : ∀ i : Fin (d.D + 1), i ≠ 0 →
      s (i, j0) = -∑ k, s (i, j0.succAbove k) * f (r (j0.succAbove k)) := by
    intro i hi
    have h1 := hrel i hi
    have e : ∀ j, s (i, j) * f (a j) = (s (i, j) * f (r j)) * f (a j0) := fun j => by
      rw [← hr j, map_mul, mul_assoc]
    simp only [e, ← Finset.sum_mul] at h1
    have h2 := (mul_eq_zero.mp h1).resolve_right hf0
    rw [Fin.sum_univ_succAbove _ j0, hr0, map_one, mul_one] at h2
    exact eq_neg_of_add_eq_zero_left h2

  let q0 : SVar d.D d.N → TVar d.D d.N :=
    Sum.elim (fun _ => ((0 : Fin (d.D + 1)), j0)) (fun ik => (ik.1, j0.succAbove ik.2))
  let t : SVar d.D d.N → OmS (Ω c) d.D d.N := fun x => s (q0 x)
  let p : TVar d.D d.N → MvPolynomial (SVar d.D d.N) (Ω c) := fun ij =>
    Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) j0
      (if ij.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (ij.1, k)) * MvPolynomial.C (r (j0.succAbove k)))
      (fun k => MvPolynomial.X (Sum.inr (ij.1, k))) ij.2
  have hpj0 : ∀ i, p (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (r (j0.succAbove k)) := by
    intro i; simp only [p, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
  have hpk : ∀ i k, p (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
    intro i k; simp only [p, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  have hpu : ∀ ij, MvPolynomial.aeval t (p ij) = s ij := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · rw [hpj0]
      split_ifs with hi
      · subst hi; simp [t, q0]
      · rw [hrel0 i hi]; simp [t, q0]; rfl
    · rw [hpk]; simp [t, q0]
  let q1 : SVar d.D d.N → TVar d.D d.N :=
    Sum.elim (fun _ => ((0 : Fin (d.D + 1)), d.jc c)) (fun ik => (ik.1, (d.jc c).succAbove ik.2))
  have hψ : ∀ P : MvPolynomial (SVar d.D d.N) (Ω c),
      MvPolynomial.aeval t (MvPolynomial.aeval (fun x => p (q1 x)) P) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P := by
    have e : (MvPolynomial.aeval t).comp (MvPolynomial.aeval (fun x => p (q1 x))) =
        IsScalarTower.toAlgHom (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom', hpu]
      rcases x with _ | ⟨i, k⟩
      · simp [q1, s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
      · simp [q1, s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
    intro P
    exact DFunLike.congr_fun e P
  refine ⟨t, fun P => ⟨_, hψ P⟩, ?_⟩
  rintro w ⟨hNZ, hpl⟩ hrint'
  have hrint : ∀ j, 0 ≤ w (f (r j)) := hrint'
  have hX0 : ∀ p, 0 ≤ w (s p) := fun p => by rw [← hOT]; exact (hpl _).1
  have ht : ∀ x, t x ∈ vRing w := fun x => hX0 _

  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) f
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap f) (algebraMap K (Ω c))
  let k₁ : IntermediateField (ResidueField (((vRing w).comap f).comap (algebraMap K (Ω c))))
      (ResidueField ((vRing w).comap f)) :=
    IntermediateField.adjoin _ {z | ∃ j, ∃ h : r j ∈ (vRing w).comap f,
      z = residue ((vRing w).comap f) ⟨r j, h⟩}
  let R3 : Subring (MvPolynomial (SVar d.D d.N) (Ω c)) :=
    ((MvPolynomial.map (algebraMap k₁ (ResidueField ((vRing w).comap f)))).range.comap
      (MvPolynomial.map (residue ((vRing w).comap f)))).map
        (MvPolynomial.map ((vRing w).comap f).subtype)
  have hR3X : ∀ x, (MvPolynomial.X x : MvPolynomial (SVar d.D d.N) (Ω c)) ∈ R3 := fun x =>
    ⟨MvPolynomial.X x, ⟨MvPolynomial.X x, by simp⟩, by simp⟩
  have hR3C : ∀ j, MvPolynomial.C (r j) ∈ R3 := fun j =>
    ⟨MvPolynomial.C ⟨r j, hrint j⟩,
      ⟨MvPolynomial.C ⟨_, IntermediateField.subset_adjoin _ _ ⟨j, hrint j, rfl⟩⟩, by simp⟩, by simp⟩
  have hpR3 : ∀ ij, p ij ∈ R3 := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · rw [hpj0]
      split_ifs
      · exact hR3X _
      · exact R3.neg_mem (R3.sum_mem fun k _ => R3.mul_mem (hR3X _) (hR3C _))
    · rw [hpk]; exact hR3X _
  have hcoefW : ∀ P ∈ R3, ∀ α, P.coeff α ∈ (vRing w).comap f := by
    intro P hP α
    obtain ⟨Q, -, rfl⟩ := hP
    rw [MvPolynomial.coeff_map]
    exact (Q.coeff α).2
  have hp : ∀ ij α, (p ij).coeff α ∈ (vRing w).comap f := fun ij α => hcoefW _ (hpR3 ij) α

  let u : TVar d.D d.N → vRing w := fun ij => ⟨s ij, hX0 ij⟩
  have hKU : algebraMap K (OmS (Ω c) d.D d.N) = f.comp (algebraMap K (Ω c)) :=
    RingHom.ext fun x => IsScalarTower.algebraMap_apply K (Ω c) _ x
  have hOT' : ∀ P, d.OTtoS c P =
      MvPolynomial.eval₂ (f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) s P := by
    intro P
    simp only [Data.OTtoS, OTtoKT, Data.sH, sHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hKU]
    rfl
  have h0 : ∀ P : MvPolynomial (TVar d.D d.N) (𝓞 K), 0 < w (MvPolynomial.eval₂
      (f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) (fun j => (u j : OmS (Ω c) d.D d.N)) P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal := by
    intro P
    show 0 < w (MvPolynomial.eval₂ _ s P) ↔ _
    rw [← hOT' P, (hpl P).2, laT, MvPolynomial.mem_map_C_iff]
  have h1 : ∀ x : 𝓞 K, 0 ≤ w ((f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) x) := by
    intro x
    have := (hpl (MvPolynomial.C x)).1
    rwa [hOT', MvPolynomial.eval₂_C] at this
  have hind_u := indep_u (Ω := Ω c) w la u h0 h1
  have hcard : Fintype.card (TVar d.D d.N) = Fintype.card (SVar d.D d.N) + d.D := by
    simp [Fintype.card_sum, Fintype.card_prod]; ring
  have RT := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K (Ω c) (OmS (Ω c) d.D d.N) d.D (hd.trdeg c)
    (SVar d.D d.N) t (vRing w) ht (TVar d.D d.N) u p hp hcard hpu hind_u
  exact ⟨ht, RT.2.2⟩
end GlobalTheory.PlaceRestrict

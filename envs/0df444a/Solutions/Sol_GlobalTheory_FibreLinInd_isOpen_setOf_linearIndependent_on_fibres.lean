-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.isOpen_setOf_linearIndependent_on_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:44.305546+00:00
-- url     : https://prove2.me/submissions/736c9234-8729-416f-a015-e045153f35d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres
import Theorems.Thm_GlobalTheory_FibreLinInd_exists_det_ne_zero
import Theorems.Thm_GlobalTheory_FibreLinInd_exists_fibrePower
import Theorems.Thm_GlobalTheory_FibreLinInd_exists_lift
import Theorems.Thm_GlobalTheory_FibreLinInd_top_le_iff
import Theorems.Thm_GlobalTheory_FibreLinInd_mem_basicOpen_iff
import Theorems.Thm_GlobalTheory_FibreLinInd_evalHom_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
variable {K : Type} [Field K] {P G : Scheme.{0}}
namespace GlobalTheory.FibreLinInd
theorem _root_.solution :
    ∀ (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G),
      L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), IsOpen {z : Z | ∀ (K : Type) [Field K]
        [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K,
          (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0} := by
  classical
  intro G Z f _ _ L _ r s
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let K := AlgebraicClosure (Z.residueField z)
  let x : Sp K ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  have hx : Set.range x = {z} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact hxt t
    · rintro rfl
      exact ⟨t₀, hxt t₀⟩
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz K x hx c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  refine ⟨p '' (O : Set P), ?_, p.isOpenMap _ O.isOpen, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ K' _ _ x' hx' c hc
    let t : Sp K' := IsLocalRing.closedPoint K'
    have ht : x' t = p w := by
      rw [← Set.mem_singleton_iff, ← hx']
      exact ⟨t, rfl⟩
    obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
    have hO : (h ≫ O.ι) t ∈ O := (h t).2
    have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
    have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
    rw [hM] at hd
    refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
    have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  · obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]
end GlobalTheory.FibreLinInd

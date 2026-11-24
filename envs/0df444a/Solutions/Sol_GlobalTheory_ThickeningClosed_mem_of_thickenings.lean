-- Prove2me | solution 1 for GlobalTheory.ThickeningClosed.mem_of_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:47.537246+00:00
-- url     : https://prove2.me/submissions/73494833-344b-45b2-8857-727646f7df83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Theorems.Thm_GlobalTheory_ThickeningClosed_ker_ideal_le_ker
import Theorems.Thm_GlobalTheory_exists_smul_eq_zero_of_mem_iInf_pow_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickeningClosed
namespace _root_.GlobalTheory.ThickeningClosed
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R)
    {X Z : Scheme.{0}} [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of R)) (ι : Z ⟶ X)
    (h : ∀ n : ℕ, ∃ l : pullback f (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n) ⟶ Z, l ≫ ι = pullback.fst f (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n))
    (x : X) (hx : I ≤ (f x).asIdeal) : x ∈ _root_.GlobalTheory.ThickeningClosed.zeroLocusOpen ι.ker := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (X.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set φ : CommRingCat.of R ⟶ Γ(X, V) := Spec.preimage (hV.fromSpec ≫ f) with hφ
  have hφ' : Spec.map φ = hV.fromSpec ≫ f := Spec.map_preimage _
  set J : Ideal Γ(X, V) := I.map φ.hom with hJ
  have hK : ∀ n : ℕ, ι.ker.ideal ⟨V, hV⟩ ≤ J ^ (n + 1) := by
    intro n
    obtain ⟨l, hl⟩ := h n
    have hle : I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ.hom :=
      Ideal.map_le_iff_le_comap.mp (Ideal.map_pow _ _ _).le
    let ψ : Γ(X, V) ⟶ CommRingCat.of (Γ(X, V) ⧸ J ^ (n + 1)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    let τ : CommRingCat.of (R ⧸ I ^ (n + 1)) ⟶ CommRingCat.of (Γ(X, V) ⧸ J ^ (n + 1)) :=
      CommRingCat.ofHom (Ideal.quotientMap _ φ.hom hle)
    have hcomm : φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk _) ≫ τ := by
      ext r; rfl
    have hsq : (Spec.map ψ ≫ hV.fromSpec) ≫ f = Spec.map τ ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n := by
      rw [Category.assoc, ← hφ', ← Spec.map_comp, hcomm, Spec.map_comp]
    have := _root_.GlobalTheory.ThickeningClosed.ker_ideal_le_ker ι hV ψ (pullback.lift _ _ hsq ≫ l)
      (by rw [Category.assoc, hl, pullback.lift_fst])
    simpa [ψ, Ideal.mk_ker] using this
  set p := hV.primeIdealOf ⟨x, hxV⟩ with hp
  have hpx : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hJp : J ≤ p.asIdeal := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    have : Spec.map φ p = f x := by rw [hφ', ← hpx]; rfl
    have h2 : (Spec.map φ p).asIdeal = p.asIdeal.comap φ.hom := rfl
    rw [← h2, this]
    exact hx
  have hkrull : ∀ a ∈ ι.ker.ideal ⟨V, hV⟩, ∃ g ∉ p.asIdeal, g * a = 0 := by
    intro a ha
    have hmem : a ∈ ⨅ n, J ^ n • (⊤ : Submodule Γ(X, V) Γ(X, V)) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) (hK n ha)
    obtain ⟨g, hg1, hga⟩ := _root_.GlobalTheory.exists_smul_eq_zero_of_mem_iInf_pow_smul J hmem
    refine ⟨g, fun hg ↦ p.2.ne_top ((Ideal.eq_top_iff_one _).mpr ?_), hga⟩
    have : g - (g - 1) ∈ p.asIdeal := Ideal.sub_mem _ hg (hJp hg1)
    simpa using this
  have hfin : ∀ t : Finset Γ(X, V), (↑t : Set Γ(X, V)) ⊆ ι.ker.ideal ⟨V, hV⟩ →
      ∃ g ∉ p.asIdeal, ∀ a ∈ t, g * a = 0 := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun h1 ↦ p.2.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert b t _ ih =>
      intro ht
      obtain ⟨g, hg, hgt⟩ := ih ((Finset.coe_subset.mpr (Finset.subset_insert b t)).trans ht)
      obtain ⟨g', hg', hg'b⟩ := hkrull b (ht (by simp))
      refine ⟨g * g', fun hm ↦ (p.2.mem_or_mem hm).elim hg hg', ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rw [mul_assoc, hg'b, mul_zero]
      · rw [mul_right_comm, hgt a ha, zero_mul]
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (ι.ker.ideal ⟨V, hV⟩) :)
  obtain ⟨g, hg, hgt⟩ := hfin t (ht ▸ Submodule.subset_span)
  have hgK : ∀ a ∈ ι.ker.ideal ⟨V, hV⟩, g * a = 0 := by
    intro a ha
    rw [← ht] at ha
    refine Submodule.span_induction (fun b hb ↦ hgt b hb) (by simp) (fun b c _ _ hb hc ↦ ?_)
      (fun r b _ hb ↦ ?_) ha
    · rw [mul_add, hb, hc, add_zero]
    · rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
  show ∃ V : X.affineOpens, x ∈ V.1 ∧ ι.ker.ideal V = ⊥
  refine ⟨X.affineBasicOpen (U := ⟨V, hV⟩) g, ?_, ?_⟩
  · have hmem : p ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hg
    rw [← hpx]; exact hmem
  · have := hV.isLocalization_basicOpen g
    rw [← ι.ker.map_ideal_basicOpen ⟨V, hV⟩ g]
    refine (Ideal.map_eq_bot_iff_le_ker _).mpr fun a ha ↦ ?_
    rw [RingHom.mem_ker]
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
      IsLocalization.Away.algebraMap_isUnit g
    have h0 := congrArg (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (hgK a ha)
    rw [map_mul, map_zero] at h0
    exact (hu.mul_right_eq_zero).mp h0
end _root_.GlobalTheory.ThickeningClosed
end GlobalTheory.ThickeningClosed

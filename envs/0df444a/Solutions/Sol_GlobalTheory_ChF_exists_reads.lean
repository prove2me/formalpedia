-- Prove2me | solution 1 for GlobalTheory.ChF.exists_reads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:18.397257+00:00
-- url     : https://prove2.me/submissions/00836036-b6a1-4a83-af42-bfb642ddd57c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesReadingGroupHomNilpotentCharts
import Theorems.Thm_GlobalTheory_evBasic_nEval_sub_coeff_mem
import Theorems.Thm_GlobalTheory_exists_series_of_natural_on_nilpotent
import Theorems.Thm_GlobalTheory_nEval_basic
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem mem_dbl {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S] {J : Ideal S}
    {x : S × S} : x ∈ dbl R J ↔ x.1 - x.2 ∈ J := by
  rw [← Ideal.Quotient.eq]; rfl
private theorem exists_coord {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] {d e : ℕ} {F : Fin d → PS R 2 d} {F' : Fin e → PS R 2 e}
    {X : Fam G d} {X' : Fam G' e} (h : NilChart G F X) (h' : NilChart G' F' X') (f : G ⟶ G') [IsMonHom f]
    (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin e → S, (∀ j, IsNilpotent (b j)) ∧ X S a ≫ f = X' S b := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range a).toFinset, by simp [J]⟩, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let ρ : dbl R J →ₐ[R] S := (AlgHom.fst R S S).comp (dbl R J).val
  let τ : dbl R J →ₐ[R] S := (AlgHom.snd R S S).comp (dbl R J).val
  let σ : S →ₐ[R] dbl R J := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun x => by
    simp [mem_dbl])
  have hker : IsNilpotent (RingHom.ker ρ) := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n + 1, le_bot_iff.1 fun x hx => ?_⟩
    have h1 : x ∈ RingHom.ker ρ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
    have h2 : RingHom.ker ρ ≤ J.comap τ := fun y hy => by
      have h3 := mem_dbl.1 y.2
      have h4 : y.1.1 = 0 := hy
      rw [h4, zero_sub, neg_mem_iff] at h3
      exact h3
    have h5 := Ideal.le_comap_pow τ (n + 1) (Ideal.pow_right_mono h2 (n + 1) hx)
    rw [pow_succ, hn, zero_mul] at h5
    exact Subtype.ext (Prod.ext h1 h5)
  let a' : Fin d → dbl R J := fun i => ⟨(0, a i), mem_dbl.2 (by
    simpa using (Ideal.subset_span ⟨i, rfl⟩ : a i ∈ J))⟩
  have hnil : ∀ y : dbl R J, ρ y = 0 → IsNilpotent y := fun y hy => by
    obtain ⟨n, hn⟩ := hker
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow (show y ∈ RingHom.ker ρ from hy) n⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ rfl
  obtain ⟨b, hb, hz⟩ := h'.surj (dbl R J) S ρ σ (by ext; rfl) hker (X _ a' ≫ f) (by
    rw [← Category.assoc, h.nat _ _ ρ a' ha']
    have : (fun i => ρ (a' i)) = 0 := rfl
    rw [this, h.zero, MonObj.one_comp])
  refine ⟨fun j => τ (b j), fun j => (hnil _ (hb j)).map τ, ?_⟩
  rw [← h'.nat _ _ τ b (fun j => hnil _ (hb j)), ← hz, ← Category.assoc, h.nat _ _ τ a' ha']
  rfl
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  intro R _ G _ _ G' _ _ d e F F' X X' h h' f hf
  classical
  choose b hb hX using exists_coord h h' f
  let c : Fin e → ∀ (S : Type) [CommRing S] [Algebra R S], (Fin 1 × Fin d → S) → S :=
    fun j S _ _ a => if ha : ∀ i, IsNilpotent (a (0, i)) then b S (fun i => a (0, i)) ha j else 0
  have hc : ∀ j (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S']
      (φ : S →ₐ[R] S') (a : Fin 1 × Fin d → S), (∀ i, IsNilpotent (a i)) →
      φ (c j S a) = c j S' (fun i => φ (a i)) := by
    intro j S _ _ S' _ _ φ a ha
    have h1 : ∀ i, IsNilpotent (a (0, i)) := fun i => ha _
    have h2 : ∀ i, IsNilpotent (φ (a (0, i))) := fun i => (ha _).map φ
    simp only [c, dif_pos h1, dif_pos h2]
    refine congrFun (h'.inj S' (fun j => φ (b S _ h1 j)) (b S' _ h2) (fun j => (hb S _ h1 j).map φ)
      (hb S' _ h2) ?_) j
    rw [← hX, ← h'.nat _ _ φ _ (hb S _ h1), ← hX, ← Category.assoc, h.nat _ _ φ _ h1]
  choose φ hφ using fun j => GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic (c j) (hc j)
  have key : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)),
      b S a ha = fun j => nv (algebraMap R S) (φ j) ![a] := by
    intro S _ inst a ha
    funext j
    have h1 := hφ j S (fun q => a q.2) (fun q => ha _)
    simp only [c, dif_pos ha] at h1
    rw [h1, nv]
    have : (algebraMap R S).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    congr 1
    funext q
    simp
  refine ⟨φ, fun j => ?_, fun S _ _ a ha => by rw [hX S a ha, key]⟩
  have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R) i) := fun _ => IsNilpotent.zero
  have h1 : b R 0 h0 = 0 := h'.inj R _ _ (hb R 0 h0) (fun _ => IsNilpotent.zero) (by
    rw [← hX, h.zero, h'.zero, MonObj.one_comp])
  have h2 := hφ j R 0 (fun _ => IsNilpotent.zero)
  have h3 : c j R 0 = 0 := by
    exact (dif_pos h0).trans (congrFun h1 j)
  have h4 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal R))
    (evBasic_nEval_sub_coeff_mem (φ j) (0 : Fin 1 × Fin d → R) (fun _ => IsNilpotent.zero))
  rw [← h2, h3] at h4
  simpa using h4
end GlobalTheory.ChF

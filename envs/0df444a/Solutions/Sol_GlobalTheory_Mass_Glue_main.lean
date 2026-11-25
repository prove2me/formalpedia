-- Prove2me | solution 1 for GlobalTheory.Mass.Glue.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:13.325308+00:00
-- url     : https://prove2.me/submissions/c9ecea21-5a0a-4100-9748-1d774d9a73c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedSubspaceComplement
import Theorems.Thm_GlobalTheory_Mass_Glue_mem_perp
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_eq_card
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_LatticeGens_gens_and_count
import Theorems.Thm_GlobalTheory_Mass_Witt_mem_perp
import Theorems.Thm_GlobalTheory_Mass_Witt_witt_definite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.Glue
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
end
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma apply_self_ne_zero_of_PD {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hpd : _root_.GlobalTheory.Mass.PD h) {x : V} (hx : x ≠ 0) : h x x ≠ 0 := by
  unfold _root_.GlobalTheory.Mass.PD at hpd
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  intro h0
  have := hpd τ x hx
  simp [h0] at this
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma nondegenerate_of_PD {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hpd : _root_.GlobalTheory.Mass.PD h) : h.Nondegenerate :=
  ⟨fun x hx => by_contra fun h0 => apply_self_ne_zero_of_PD hpd h0 (hx x),
    fun y hy => by_contra fun h0 => apply_self_ne_zero_of_PD hpd h0 (hy y)⟩
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma idxN_dual_hRes_ne_zero_of_isIntLat [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hK : _root_.Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hpd : _root_.GlobalTheory.Mass.PD h)
    (W : Submodule K V) {A : Submodule (𝓞 K) W}
    (hA : _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h W) A) :
    _root_.GlobalTheory.Mass.idxN (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h W) A) A ≠ 0 := by
  have hw := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hpd).2 W
  have := (_root_.GlobalTheory.Mass.DiscOrder.main K W _ hK hw.2.1
    (nondegenerate_of_PD hw.2.2.1) A hA).1
  unfold _root_.GlobalTheory.Mass.discN at this
  exact this
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma index_sup_map_le_lemma_2 {W₁ W₂ : Submodule K V} {A₁ A₁' : Submodule (𝓞 K) W₁}
    {A₂ A₂' : Submodule (𝓞 K) W₂}
    (hn : _root_.GlobalTheory.Mass.idxN A₁' A₁ * _root_.GlobalTheory.Mass.idxN A₂' A₂ ≠ 0) :
    _root_.GlobalTheory.Mass.idxN
        (A₁'.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂'.map (W₂.subtype.restrictScalars (𝓞 K)))
        (A₁.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂.map (W₂.subtype.restrictScalars (𝓞 K))) ≤
      _root_.GlobalTheory.Mass.idxN A₁' A₁ * _root_.GlobalTheory.Mass.idxN A₂' A₂ ∧
    _root_.GlobalTheory.Mass.idxN
        (A₁'.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂'.map (W₂.subtype.restrictScalars (𝓞 K)))
        (A₁.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂.map (W₂.subtype.restrictScalars (𝓞 K))) ≠ 0 := by
  simp only [_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_card] at hn ⊢
  rw [← Nat.card_prod] at hn ⊢
  let ι₁ := W₁.subtype.restrictScalars (𝓞 K)
  let ι₂ := W₂.subtype.restrictScalars (𝓞 K)
  let Y := A₁'.map ι₁ ⊔ A₂'.map ι₂
  let X := A₁.map ι₁ ⊔ A₂.map ι₂
  let Z := Submodule.comap Y.subtype X
  let φ₁ : A₁' →ₗ[𝓞 K] Y ⧸ Z := Z.mkQ ∘ₗ LinearMap.codRestrict Y (ι₁ ∘ₗ A₁'.subtype)
    (fun x => Submodule.mem_sup_left (Submodule.mem_map_of_mem x.2))
  let φ₂ : A₂' →ₗ[𝓞 K] Y ⧸ Z := Z.mkQ ∘ₗ LinearMap.codRestrict Y (ι₂ ∘ₗ A₂'.subtype)
    (fun x => Submodule.mem_sup_right (Submodule.mem_map_of_mem x.2))
  let g₁ := (Submodule.comap A₁'.subtype A₁).liftQ φ₁ (fun x hx => by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)))
  let g₂ := (Submodule.comap A₂'.subtype A₂).liftQ φ₂ (fun x hx => by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem hx)))
  let G : (A₁' ⧸ Submodule.comap A₁'.subtype A₁) × (A₂' ⧸ Submodule.comap A₂'.subtype A₂) →
      Y ⧸ Z := fun p => g₁ p.1 + g₂ p.2
  have hG : Function.Surjective G := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective Z z
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 y.2
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Submodule.mem_map.1 hb
    refine ⟨(Submodule.Quotient.mk ⟨a₀, ha₀⟩, Submodule.Quotient.mk ⟨b₀, hb₀⟩), ?_⟩
    simp only [G, g₁, g₂, Submodule.liftQ_apply, φ₁, φ₂, LinearMap.comp_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext hab
  haveI : Finite ((A₁' ⧸ Submodule.comap A₁'.subtype A₁) ×
      (A₂' ⧸ Submodule.comap A₂'.subtype A₂)) := Nat.finite_of_card_ne_zero hn
  haveI : Finite (Y ⧸ Z) := Finite.of_surjective G hG
  haveI : Nonempty (Y ⧸ Z) := ⟨0⟩
  exact ⟨Nat.card_le_card_of_surjective G hG, Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩⟩
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma le_dual_of_apply_mem_one (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V}
    (hL : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) : L ≤ _root_.Formalism.HermitianLatticesTheory.dual h L := by
  intro y hy
  rw [_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro x hx
  exact hL x hx y hy
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma apply_mem_one_of_isIntLat {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : _root_.GlobalTheory.Mass.IsIntLat h L) :
    ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K) := by
  unfold _root_.GlobalTheory.Mass.IsIntLat at hL
  have := hL.2
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat at this
  exact this
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma mem_latIn_iff {W : Submodule K V} {L : Submodule (𝓞 K) V}
    {x : W} : x ∈ _root_.GlobalTheory.Mass.latIn W L ↔ (x : V) ∈ L := by
  unfold _root_.GlobalTheory.Mass.latIn; exact Iff.rfl
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma hRes_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (x y : W) : _root_.GlobalTheory.Mass.hRes h W x y = h x y := by
  unfold _root_.GlobalTheory.Mass.hRes; rfl
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma apply_eq_zero_of_mem_perp {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {W : Submodule K V} {x w : V} (hx : x ∈ W) (hw : w ∈ _root_.GlobalTheory.Mass.perp h W) :
    h w x = 0 := by
  rw [← hs.eq x w, (_root_.GlobalTheory.Mass.Witt.mem_perp h W w).1 hw x hx, map_zero]
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
private lemma le_sup_map_dual_latIn_perp {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {W : Submodule K V}
    (hc : IsCompl W (_root_.GlobalTheory.Mass.perp h W)) {L : Submodule (𝓞 K) V}
    (hL : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) :
    L ≤ (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h W) (_root_.GlobalTheory.Mass.latIn W L)).map
        (W.subtype.restrictScalars (𝓞 K)) ⊔
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h W))
        (_root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h W) L)).map
        ((_root_.GlobalTheory.Mass.perp h W).subtype.restrictScalars (𝓞 K)) := by
  intro x hx
  have hxs : x ∈ W ⊔ _root_.GlobalTheory.Mass.perp h W := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hxs
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨⟨u, hu⟩, ?_, rfl⟩)
    (Submodule.mem_map.2 ⟨⟨w, hw⟩, ?_, rfl⟩)
  · rw [_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hyL := hL _ (mem_latIn_iff.1 hy) _ hx
    rw [map_add, (_root_.GlobalTheory.Mass.Witt.mem_perp h W w).1 hw _ y.2, add_zero] at hyL
    rw [hRes_apply]
    exact hyL
  · rw [_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hyL := hL _ (mem_latIn_iff.1 hy) _ hx
    rw [map_add, apply_eq_zero_of_mem_perp hs hu y.2, zero_add] at hyL
    rw [hRes_apply]
    exact hyL
end GlobalTheory.Mass.Glue
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Glue
open NumberField Matrix
open scoped ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.Glue
namespace _root_.GlobalTheory.Mass.Glue
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U)
    (B : Submodule (𝓞 K) (_root_.GlobalTheory.Mass.perp h U)) (e e' : ℕ),
    _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h U) A →
    _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B →
    (∃ t : Finset ↥U, t.card ≤ e ∧ _root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A =
      A ⊔ Submodule.span (𝓞 K) (t : Set _)) →
    (∃ t : Finset ↥(_root_.GlobalTheory.Mass.perp h U), t.card ≤ e' ∧
      _root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B =
        B ⊔ Submodule.span (𝓞 K) (t : Set _)) →
    {L : Submodule (𝓞 K) V | _root_.GlobalTheory.Mass.IsIntLat h L ∧ _root_.GlobalTheory.Mass.latIn U L = A ∧
      _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) L = B}.encard ≤
      (((_root_.GlobalTheory.Mass.discN (_root_.GlobalTheory.Mass.hRes h U) A *
        _root_.GlobalTheory.Mass.discN
          (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd U A B e e' hA hB ⟨t, ht, htA⟩ ⟨t', ht', htB⟩
  have hc := ((_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hpd).2 U).1
  have hdA := idxN_dual_hRes_ne_zero_of_isIntLat hK hs hpd U hA
  have hdB := idxN_dual_hRes_ne_zero_of_isIntLat hK hs hpd _ hB
  unfold _root_.GlobalTheory.Mass.discN
  obtain ⟨hle, hne⟩ := index_sup_map_le_lemma_2 (A₁ := A) (A₁' := _root_.Formalism.HermitianLatticesTheory.dual _ A) (A₂ := B)
    (A₂' := _root_.Formalism.HermitianLatticesTheory.dual _ B) (mul_ne_zero hdA hdB)
  have hXY : A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
      B.map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)) ≤
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A).map (U.subtype.restrictScalars (𝓞 K)) ⊔
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B).map
        ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)) :=
    sup_le_sup (Submodule.map_mono (le_dual_of_apply_mem_one _ (apply_mem_one_of_isIntLat hA)))
      (Submodule.map_mono (le_dual_of_apply_mem_one _ (apply_mem_one_of_isIntLat hB)))
  have hT : (t.image Subtype.val ∪ t'.image Subtype.val).card ≤ e + e' :=
    (Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_image_le.trans ht) (Finset.card_image_le.trans ht'))
  have hY : (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A).map
      (U.subtype.restrictScalars (𝓞 K)) ⊔
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B).map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)) =
      (A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
        B.map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K))) ⊔
      Submodule.span (𝓞 K) ((t.image Subtype.val ∪ t'.image Subtype.val : Finset V) : Set V) := by
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Submodule.span_union, htA, htB,
      Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Submodule.map_span]
    exact sup_sup_sup_comm _ _ _ _
  have hcount := ((_root_.GlobalTheory.Mass.LatticeGens.gens_and_count K V _ _ hXY hne).2 (e + e') _
    hT hY).1
  have hpow : ((_root_.GlobalTheory.Mass.idxN
      ((_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A).map (U.subtype.restrictScalars (𝓞 K)) ⊔
        (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B).map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)))
      (A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
        B.map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K))) ^ (e + e')
        : ℕ) : ℕ∞) ≤
      (((_root_.GlobalTheory.Mass.idxN (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A) A *
        _root_.GlobalTheory.Mass.idxN (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h
          (_root_.GlobalTheory.Mass.perp h U)) B) B) ^ (e + e') : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.pow_le_pow_left hle (e + e')
  refine le_trans (Set.encard_le_encard ?_) (hcount.trans hpow)
  rintro L ⟨hL, hLU, hLP⟩
  refine ⟨sup_le ?_ ?_, ?_⟩
  · rw [Submodule.map_le_iff_le_comap, ← hLU]
    unfold _root_.GlobalTheory.Mass.latIn
    exact le_rfl
  · rw [Submodule.map_le_iff_le_comap, ← hLP]
    unfold _root_.GlobalTheory.Mass.latIn
    exact le_rfl
  · have := le_sup_map_dual_latIn_perp hs hc (apply_mem_one_of_isIntLat hL)
    rw [hLU, hLP] at this
    exact this
end _root_.GlobalTheory.Mass.Glue
end GlobalTheory.Mass.Glue

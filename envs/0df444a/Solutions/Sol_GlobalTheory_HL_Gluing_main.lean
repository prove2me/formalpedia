-- Prove2me | solution 1 for GlobalTheory.HL.Gluing.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:27.480052+00:00
-- url     : https://prove2.me/submissions/6a13584c-3756-4fcf-827f-5bde92ec5987

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ComplementLatticeOfTermFreeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGluingHomomorphismDefectGroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_CompLat_main
import Theorems.Thm_GlobalTheory_HL_StdLat_stdLat_spec
import Theorems.Thm_GlobalTheory_HL_TermBasic_inner_smul
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_top
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.Gluing
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} {S : Frames L r k}
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem exists_tauRel_of_mem_complementLattice (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) :
    ∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ,
      S.TauRel d Λ w y := by
  obtain ⟨p, -, -, -, -, -, -, -, hgr⟩ := hT
  obtain ⟨-, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hθ : (algebraMap F E) S.th⁻¹ * (algebraMap F E) S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  rintro w ⟨-, -, -, hw⟩
  rw [hgr] at hw
  obtain ⟨y', hy', y, hy, -, -, hx', hx, t, ht, e⟩ := hw
  have hX : S.X ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.X
    exact le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r))
  have hX' : S.X' ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.X'
    exact le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r))
  have htt : (algebraMap F E) S.th⁻¹ • (y' - y) = t := by
    rw [e, smul_smul, hθ, one_smul]
  refine ⟨t, ?_, y - w, hx, y' - w, hx', by simpa using hy, by simpa using hy', ⟨t, ht, ?_⟩, ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.sat
    refine Submodule.mem_inf.2 ⟨ht, ?_⟩
    rw [Submodule.restrictScalars_mem, ← htt]
    refine S.ME.smul_mem _ ?_
    have := S.ME.sub_mem (hX' hx') (hX hx)
    simpa using this
  · simpa using e
  · have : y' - w - (y - w) = y' - y := by abel
    rw [this, htt, sub_self]
    exact Submodule.zero_mem _
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem tauRel_iff_sub_mem_M (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) :
    ∀ w y y', S.TauRel d Λ w y →
      (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ) := by
  obtain ⟨-, -, hMsat, hf, hf', -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  set θ : E := (algebraMap F E) S.th⁻¹ with hθdef
  have hθ : θ * (algebraMap F E) S.th = 1 := by
    rw [hθdef, ← map_mul, inv_mul_cancel₀ hth, map_one]
  have hMΛ : ∀ x, x ∈ S.M d Λ → x ∈ Λ :=
    fun x hx => (Submodule.mem_inf.1 (hMsat hx)).1
  have hMdef : S.M d Λ = Submodule.span L.O (Set.range (S.fr d Λ) ∪
      Set.range fun b => θ • (S.fr' d Λ b - S.fr d Λ b)) := rfl
  have hfr : ∀ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}),
      x ∈ S.M d Λ := by
    rw [hMdef]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, -, rfl⟩
    exact Or.inl ⟨i, rfl⟩
  have hclaim : ∀ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < r}),
      ∃ z ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}),
        θ • (x - z) ∈ S.M d Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨S.fr d Λ i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩
      rw [hMdef]
      exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hxz⟩ := hx
      obtain ⟨z', hz', hyz⟩ := hy
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      rw [add_sub_add_comm, smul_add]
      exact Submodule.add_mem _ hxz hyz
    | smul c x _ hx =>
      obtain ⟨z, hz, hxz⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [← smul_sub, smul_comm]
      exact Submodule.smul_mem _ c hxz
  intro w y y' ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, hy⟩
  constructor
  · rintro ⟨b, hb, b', hb', n, n', ⟨u, hu, eu⟩, hy'⟩
    have hα : a - b ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < r}) := by
      refine (hf r (Nat.le_succ r) _).1 ⟨?_, S.X.sub_mem ha hb⟩
      have := Λ.sub_mem m n
      simpa using this
    have hα' : a' - b' ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < r}) := by
      refine (hf' r (Nat.le_succ r) _).1 ⟨?_, S.X'.sub_mem ha' hb'⟩
      have := Λ.sub_mem m' n'
      simpa using this
    obtain ⟨z, hz, hz'⟩ := hclaim _ hα'
    have hts : θ • ((a' - a) - (b' - b)) = t - u := by
      rw [et, eu, ← smul_sub, smul_smul, hθ, one_smul]
    have hβ : θ • (z - (a - b)) ∈ S.M d Λ := by
      apply hfr
      refine (hf r (Nat.le_succ r) _).1 ⟨?_, ?_⟩
      · have h1 : θ • (z - (a - b)) = (t - u) - θ • (a' - b' - z) := by
          rw [← hts, ← smul_sub]; congr 1; abel
        rw [h1]
        exact Λ.sub_mem (Λ.sub_mem ht hu) (hMΛ _ hz')
      · refine S.X.smul_mem θ
          (S.X.sub_mem ?_ (S.X.sub_mem ha hb))
        exact ((hf r (Nat.le_succ r) _).2 hz).2
    have h2 : y - y' = (y - θ • (a' - a)) - (y' - θ • (b' - b)) +
        (θ • (a' - b' - z) + θ • (z - (a - b))) := by
      have h3 : a' - b' - z + (z - (a - b)) = (a' - a) - (b' - b) := by abel
      rw [← smul_add, h3]
      module
    rw [h2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ hy hy') (Submodule.add_mem _ hz' hβ)
  · intro hyy
    refine ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, ?_⟩
    have : y' - θ • (a' - a) = (y - θ • (a' - a)) - (y - y') := by abel
    rw [this]
    exact Submodule.sub_mem _ hy hyy
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem tauRel_smul_add (d : S.Datum)
    (Λ : Submodule L.O S.V) (c : E) (hc : c ∈ L.O) (w₁ w₂ y₁ y₂ : S.V)
    (h₁ : S.TauRel d Λ w₁ y₁) (h₂ : S.TauRel d Λ w₂ y₂) :
    S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂) := by
  have hs : ∀ v : S.V, (⟨c, hc⟩ : L.O) • v = c • v := fun _ => rfl
  obtain ⟨a, ha, a', ha', m, m', ⟨t, ht, et⟩, hy⟩ := h₁
  obtain ⟨b, hb, b', hb', n, n', ⟨u, hu, eu⟩, hz⟩ := h₂
  refine ⟨c • a + b, S.X.add_mem (S.X.smul_mem c ha) hb,
    c • a' + b', S.X'.add_mem (S.X'.smul_mem c ha') hb',
    ?_, ?_, ⟨(⟨c, hc⟩ : L.O) • t + u, Λ.add_mem (Λ.smul_mem _ ht) hu, ?_⟩, ?_⟩
  · have := Λ.add_mem (Λ.smul_mem (⟨c, hc⟩ : L.O) m) n
    rw [hs] at this
    convert this using 1
    module
  · have := Λ.add_mem (Λ.smul_mem (⟨c, hc⟩ : L.O) m') n'
    rw [hs] at this
    convert this using 1
    module
  · rw [hs, smul_add, smul_comm _ c t, ← et, ← eu]
    module
  · have := (S.M d Λ).add_mem ((S.M d Λ).smul_mem (⟨c, hc⟩ : L.O) hy) hz
    rw [hs] at this
    convert this using 1
    module
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem mem_complementLattice_of_mem_term (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (w : S.V)
    (hw : w ∈ S.W0) (hΛ : w ∈ Λ) :
    w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0 := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛn, hΛn', -, hgr⟩ := hT
  have hME : ∀ x ∈ S.ME, S.h w x = 0 := hw
  have hXo : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X := fun x hx =>
    hME x (le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx)
  have hXo' : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X' := fun x hx =>
    hME x (le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)) hx)
  refine ⟨⟨hw, ?_, ?_, ?_⟩, ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simpa using hΛ,
    by simpa using hΛ, ⟨0, Λ.zero_mem, by simp⟩, by simpa using Submodule.zero_mem _⟩⟩
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn w).2 ⟨w, ?_, hXo, by simpa using Submodule.zero_mem _⟩
    rw [← hΛn]; exact hΛ
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn' w).2 ⟨w, ?_, hXo', by simpa using Submodule.zero_mem _⟩
    rw [← hΛn']; exact hΛ
  · rw [hgr]
    exact ⟨w, hΛ, w, hΛ, hXo', hXo, by simpa using Submodule.zero_mem _,
      by simpa using Submodule.zero_mem _, 0, Λ.zero_mem, by simp⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem mem_of_tauRel_zero (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (w : S.V)
    (hτ : S.TauRel d Λ w 0) : w ∈ Λ := by
  obtain ⟨-, -, -, hf, hf', -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hli, -, -, -, -, hth, hthO, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hdis := (linearIndependent_sum.1 hli).2.2
  set θ : E := (algebraMap F E) S.th⁻¹ with hθdef
  set τ : E := (algebraMap F E) S.th with hτdef
  have hτθ : τ * θ = 1 := by
    rw [hθdef, hτdef, ← map_mul, mul_inv_cancel₀ hth, map_one]
  have hτO : τ ∈ L.O := (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 hthO
  have hMdef : S.M d Λ = Submodule.span L.O (Set.range (S.fr d Λ) ∪
      Set.range fun b => θ • (S.fr' d Λ b - S.fr d Λ b)) := rfl
  have hfrf : ∀ i, S.fr d Λ i ∈ Λ ∧ S.fr d Λ i ∈ Submodule.span E (Set.range S.f) := by
    intro i
    have := (hf (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.isLt, rfl⟩)
    rw [_root_.GlobalTheory.HL.TermBasic.spanTo_top] at this
    exact this
  have hfr' : ∀ i, S.fr' d Λ i ∈ Submodule.span E (Set.range S.f') := by
    intro i
    have := (hf' (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.isLt, rfl⟩)
    rw [_root_.GlobalTheory.HL.TermBasic.spanTo_top] at this
    exact this.2
  have hclaim : ∀ δ ∈ S.M d Λ, ∃ p ∈ Λ, p ∈ Submodule.span E (Set.range S.f) ∧
      ∃ q ∈ Submodule.span E (Set.range S.f'), τ • δ = q - p := by
    intro δ hδ
    rw [hMdef] at hδ
    induction hδ using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · refine ⟨-(τ • S.fr d Λ i), Λ.neg_mem (Λ.smul_mem (⟨τ, hτO⟩ : L.O) (hfrf i).1),
          Submodule.neg_mem _ (Submodule.smul_mem _ τ (hfrf i).2), 0, Submodule.zero_mem _, by simp⟩
      · refine ⟨S.fr d Λ i, (hfrf i).1, (hfrf i).2, S.fr' d Λ i, hfr' i, ?_⟩
        rw [smul_smul, hτθ, one_smul]
    | zero => exact ⟨0, Λ.zero_mem, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp, hpf, q, hq, e⟩ := hx
      obtain ⟨p', hp', hpf', q', hq', e'⟩ := hy
      refine ⟨p + p', Λ.add_mem hp hp', Submodule.add_mem _ hpf hpf', q + q',
        Submodule.add_mem _ hq hq', ?_⟩
      rw [smul_add, e, e']; abel
    | smul c x _ hx =>
      obtain ⟨p, hp, hpf, q, hq, e⟩ := hx
      refine ⟨c • p, Λ.smul_mem c hp, Submodule.smul_mem _ (c : E) hpf, (c : E) • q,
        Submodule.smul_mem _ (c : E) hq, ?_⟩
      change τ • ((c : E) • x) = (c : E) • q - (c : E) • p
      rw [smul_comm, e, smul_sub]
  obtain ⟨a, ha, a', ha', m, -, -, hy⟩ := hτ
  have hδ : θ • (a' - a) ∈ S.M d Λ := by
    have := (S.M d Λ).neg_mem hy
    rwa [zero_sub, neg_neg] at this
  obtain ⟨p, hp, hpf, q, hq, e⟩ := hclaim _ hδ
  rw [smul_smul, hτθ, one_smul] at e
  have haf : a ∈ Submodule.span E (Set.range S.f) := by
    rw [← _root_.GlobalTheory.HL.TermBasic.spanTo_top S S.f]
    exact _root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r) ha
  have haf' : a' ∈ Submodule.span E (Set.range S.f') := by
    rw [← _root_.GlobalTheory.HL.TermBasic.spanTo_top S S.f']
    exact _root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r) ha'
  have h0 : a - p = a' - q := by
    have h1 : a - p - (a' - q) = -((a' - a) - (q - p)) := by abel
    rw [← sub_eq_zero, h1, e, sub_self, neg_zero]
  have hz : a - p = 0 := by
    refine (Submodule.disjoint_def.1 hdis) _ (Submodule.sub_mem _ haf hpf) ?_
    rw [h0]; exact Submodule.sub_mem _ haf' hq
  have hap : a = p := sub_eq_zero.1 hz
  have := Λ.sub_mem m (hap ▸ hp)
  simpa using this
end GlobalTheory.HL.Gluing
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Gluing
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} {S : Frames L r k}
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} {S : _root_.GlobalTheory.HL.Frames L r k}
namespace GlobalTheory.HL.Gluing
namespace _root_.GlobalTheory.HL.Gluing
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ w ∈ S.complementLatticeOfDatum d, ∃ y ∈ S.sat Λ, S.TauRel d Λ w y) ∧ (∀ w y y', S.TauRel d Λ w y → (S.TauRel d Λ w y' ↔ y - y' ∈ S.M d Λ)) ∧ (∀ c ∈ L.O, ∀ w₁ w₂ y₁ y₂, S.TauRel d Λ w₁ y₁ → S.TauRel d Λ w₂ y₂ → S.TauRel d Λ (c • w₁ + w₂) (c • y₁ + y₂)) ∧ (∀ w ∈ S.W0, w ∈ Λ ↔ (w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0)) ∧ S.Ihat d Λ ≤ S.sat Λ ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have h1 := exists_tauRel_of_mem_complementLattice S d Λ hT
  have h2 := tauRel_iff_sub_mem_M S d Λ hT
  have hMsat := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  refine ⟨h1, h2, fun c hc w₁ w₂ y₁ y₂ => tauRel_smul_add S d Λ c hc w₁ w₂ y₁ y₂,
    fun w hw => ⟨mem_complementLattice_of_mem_term S d Λ hT w hw,
      fun h => mem_of_tauRel_zero S d Λ hT w h.2⟩, ?_,
    _root_.GlobalTheory.HL.CompLat.main L r k S d Λ hT⟩
  unfold _root_.GlobalTheory.HL.Frames.Ihat
  refine sup_le hMsat (Submodule.span_le.2 ?_)
  rintro y ⟨w, hw, hwy⟩
  obtain ⟨y₀, hy₀, hwy₀⟩ := h1 w hw
  have hd : y₀ - y ∈ S.M d Λ := (h2 w y₀ y hwy₀).1 hwy
  have : y = y₀ - (y₀ - y) := by abel
  rw [this]
  exact (S.sat Λ).sub_mem hy₀ (hMsat hd)
end _root_.GlobalTheory.HL.Gluing
end GlobalTheory.HL.Gluing

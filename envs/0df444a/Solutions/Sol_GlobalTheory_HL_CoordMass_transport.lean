-- Prove2me | solution 1 for GlobalTheory.HL.CoordMass.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:00.897927+00:00
-- url     : https://prove2.me/submissions/fae143ba-920e-4743-be9b-a68f0d33b78c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMass
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_CoordUnip_grp_apply
import Theorems.Thm_GlobalTheory_HL_CoordUnip_transport
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_matrix
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.CoordMass
open GlobalTheory.HL.Eichler GlobalTheory.HL.CoordUnip
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
end
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private lemma hf_sum_smul_left {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {m : ℕ}
    (Hm : Matrix (Fin m) (Fin m) E) {ι : Type} [Fintype ι] (c : ι → E) (g : ι → Fin m → E)
    (y : Fin m → E) :
    _root_.GlobalTheory.HL.hf L Hm (∑ i, c i • g i : Fin m → E) y =
      ∑ i, c i * _root_.GlobalTheory.HL.hf L Hm (g i) y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦
    Finset.sum_congr rfl fun l _ ↦ ?_
  ring
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private lemma unipotent_pairing_integral_iff_mem_stabilizer_lemma {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) (g : Fin (r + 1) → S.V)
    (es : Fin r → S.V) (T : Fˣ)
    (hg : ∀ a b, _root_.GlobalTheory.HL.hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E) ↑T else 0)
    (hes : ∀ a j, _root_.GlobalTheory.HL.hf L S.Hm (g a) (es j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) :
    (∀ (a : Fin r) (b : Fin (r + 1)), _root_.GlobalTheory.HL.hf L S.Hm (n (g b)) (es a) ∈ L.O) ↔
      n ∈ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range g)) := by
  obtain ⟨s, ⟨hlow, hdiag⟩, hns⟩ := _root_.GlobalTheory.HL.FrameOnto.exists_matrix S g T hg n hn
  have hpair : ∀ (c : Fin (r + 1) → E) (a : Fin r),
      _root_.GlobalTheory.HL.hf L S.Hm (∑ i, c i • g i) (es a) = c a.castSucc := by
    intro c a
    rw [hf_sum_smul_left]
    simp [hes]
  have hform : ∀ a b, _root_.GlobalTheory.HL.hf L S.Hm (n (g b)) (es a) = s a.castSucc b := by
    intro a b
    rw [hns b, hpair]
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hint
    have hcoef : ∀ i b, s i b ∈ L.O := by
      intro i b
      induction i using Fin.lastCases with
      | last =>
        rcases lt_or_eq_of_le (Fin.le_last b) with hb | hb
        · rw [hlow _ _ hb]
          exact zero_mem _
        · rw [hb, hdiag]
          exact one_mem _
      | cast a =>
        rw [← hform]
        exact hint a b
    set Λ := Submodule.span L.O (Set.range g)
    have hle : Λ ≤ Λ.comap ((n.restrictScalars L.O : S.V ≃ₗ[L.O] S.V) : S.V →ₗ[L.O] S.V) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      change n (g j) ∈ Λ
      rw [hns j]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      exact Submodule.smul_mem Λ (⟨s i j, hcoef i j⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)
    have hsub : n • Λ ≤ Λ := Submodule.map_le_iff_le_comap.2 hle
    have hsup : Λ ≤ n • Λ := by
      have key : ∀ m : ℕ, ∀ j : Fin (r + 1), (j : ℕ) < m → g j ∈ n • Λ := by
        intro m
        induction m with
        | zero => intro j hj; omega
        | succ m ih =>
          intro j hj
          have hnj : n (g j) ∈ n • Λ :=
            Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
          have hsplit : n (g j) = g j + ∑ i ∈ Finset.univ.erase j, s i j • g i := by
            rw [hns j, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hdiag, one_smul]
          have hrest : ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ n • Λ := by
            refine Submodule.sum_mem _ fun i hi ↦ ?_
            rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hij | hij
            · have hgi := ih i (by have := Fin.lt_def.1 hij; omega)
              exact Submodule.smul_mem _ (⟨s i j, hcoef i j⟩ : L.O) hgi
            · rw [hlow _ _ hij, zero_smul]
              exact zero_mem _
          have : g j = n (g j) - ∑ i ∈ Finset.univ.erase j, s i j • g i := by
            rw [hsplit]
            abel
          rw [this]
          exact Submodule.sub_mem _ hnj hrest
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      exact key (j + 1) j (Nat.lt_succ_self _)
    exact le_antisymm hsub hsup
  · intro hstab a b
    have hmem : n (g b) ∈ Submodule.span L.O (Set.range g) := by
      rw [← hstab]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨b, rfl⟩)
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hmem
    rw [← hd]
    have : (∑ i, d i • g i) = ∑ i, (d i : E) • g i := rfl
    rw [this, hpair]
    exact (d a.castSucc).2
end GlobalTheory.HL.CoordMass
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordMass
open GlobalTheory.HL.Eichler GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
open ValuativeRel
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.CoordMass
namespace _root_.GlobalTheory.HL.CoordMass
theorem _root_.solution :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r),
      ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
        (∀ g, g ∈ P.UW0 ↔ c.grp g ∈ S.H0) ∧
          (∀ g, g ∈ P.K0 ↔ c.grp g ∈ S.K0) ∧
          Function.Bijective c.lat ∧
          (∀ g Λ, c.lat (_root_.Formalism.MainNotions.S.LocNG.img g Λ) =
            c.grp g • c.lat Λ) ∧
          (∀ g Λ, g ∈ _root_.Formalism.MainNotions.S.LocNG.Aut Λ ↔ c.grp g ∈
            MulAction.stabilizer S.GLV (c.lat Λ)) ∧
          ∀ t : _root_.Formalism.MainNotions.S.Loc.Term V M r, _root_.Formalism.MainNotions.S.LocNG.mu P t = S.mu (c.lat t.abelian₂) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P S c
  have hSt : ∀ g, g ∈ P.St ↔ c.grp g ∈ S.St :=
    (_root_.GlobalTheory.HL.CoordUnip.transport M hOK H r k P S c).2.2.2.1
  have hconj : ∀ g v, c.grp g (c.e v) =
      c.e (g v) := _root_.GlobalTheory.HL.CoordUnip.grp_apply c
  have hinj : Function.Injective c.lat :=
    Submodule.map_injective_of_injective
      (f := ((c.e.restrictScalars M.L.O : V ≃ₗ[M.L.O] S.V) : V →ₗ[M.L.O] S.V))
      c.e.injective
  have hsurj : Function.Surjective c.lat :=
    Submodule.map_surjective_of_surjective
      (f := ((c.e.restrictScalars M.L.O : V ≃ₗ[M.L.O] S.V) : V →ₗ[M.L.O] S.V))
      c.e.surjective
  have hequiv : ∀ g Λ, c.lat (_root_.Formalism.MainNotions.S.LocNG.img g Λ) =
      c.grp g • c.lat Λ := by
    intro g Λ
    change (Λ.map _).map _ = (Λ.map _).map _
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    ext v
    simp [hconj]
  have hAut : ∀ g Λ, g ∈ _root_.Formalism.MainNotions.S.LocNG.Aut Λ ↔ c.grp g ∈
      MulAction.stabilizer S.GLV (c.lat Λ) := by
    intro g Λ
    have hcl : _root_.Formalism.MainNotions.S.LocNG.Aut Λ = (MulAction.stabilizer S.GLV (c.lat Λ)).comap
        c.grp.toMonoidHom := by
      unfold _root_.Formalism.MainNotions.S.LocNG.Aut
      refine le_antisymm ((Subgroup.closure_le _).2 fun g hg ↦ ?_)
        (fun g hg ↦ Subgroup.subset_closure ?_)
      · change c.grp g • c.lat Λ = c.lat Λ
        rw [← hequiv]
        exact congrArg c.lat hg
      · change c.grp g • c.lat Λ =
          c.lat Λ at hg
        rw [← hequiv] at hg
        exact hinj hg
    rw [hcl]
    rfl
  have hS : ∀ x y, S.h x y = _root_.GlobalTheory.HL.hf M.L S.Hm x y := fun _ _ ↦ rfl
  have hH0 : ∀ g, c.grp g ∈ S.H0 ↔
      ((∀ x y, H.h (g x) (g y) = H.h x y) ∧
        ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b) := by
    intro g
    have hfix : (∀ v ∈ S.ME, c.grp g v = v) ↔
        ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
      constructor
      · intro h b
        have hf : S.f b ∈ S.ME := Submodule.mem_sup_left
          (_root_.GlobalTheory.HL.FrameOnto.mem_spanTo S S.f (i := b) b.isLt)
        have hf' : S.f' b ∈ S.ME := Submodule.mem_sup_right
          (_root_.GlobalTheory.HL.FrameOnto.mem_spanTo S S.f' (i := b) b.isLt)
        have h1 := h _ hf
        have h2 := h _ hf'
        rw [c.f_eq, hconj] at h1
        rw [c.f'_eq, hconj] at h2
        exact ⟨c.e.injective h1, c.e.injective h2⟩
      · intro h v hv
        have hle : S.ME ≤ LinearMap.eqLocus
            ((c.grp g : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V)
            LinearMap.id := by
          unfold _root_.GlobalTheory.HL.Frames.ME _root_.GlobalTheory.HL.Frames.spanTo
          refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
          · rintro _ ⟨b, -, rfl⟩
            change c.grp g (S.f b) = S.f b
            rw [c.f_eq, hconj, (h b).1]
          · rintro _ ⟨b, -, rfl⟩
            change c.grp g (S.f' b) = S.f' b
            rw [c.f'_eq, hconj, (h b).2]
        exact hle hv
    unfold _root_.GlobalTheory.HL.Frames.H0
    rw [Subgroup.mem_inf, ← hfix]
    unfold _root_.GlobalTheory.HL.isomG _root_.GlobalTheory.HL.unipOn
    simp only [Subgroup.mem_mk, Set.mem_setOf_eq, Submodule.mem_bot, sub_eq_zero]
    constructor
    · rintro ⟨hiso, -, hfx⟩
      refine ⟨fun x y ↦ ?_, hfx⟩
      rw [← c.h_eq, ← hconj, ← hconj, hS, hiso, ← hS, c.h_eq]
    · rintro ⟨hiso, hfx⟩
      refine ⟨fun x y ↦ ?_, fun v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩, hfx⟩
      · obtain ⟨x, rfl⟩ := c.e.surjective x
        obtain ⟨y, rfl⟩ := c.e.surjective y
        rw [← hS, ← hS, hconj, hconj, c.h_eq, c.h_eq, hiso]
      · have := hfx _ hv
        rw [(c.grp g).injective this] at hv
        exact hv
      · rw [hfx v hv]
        exact hv
  have hUW0 : ∀ g, g ∈ P.UW0 ↔ c.grp g ∈ S.H0 := by
    intro g
    have hcl : P.UW0 = S.H0.comap c.grp.toMonoidHom := by
      unfold _root_.Formalism.MainNotions.S.LocNG.FPair.UW0
      refine le_antisymm ((Subgroup.closure_le _).2 fun g hg ↦ ?_)
        (fun g hg ↦ Subgroup.subset_closure ?_)
      · exact (hH0 g).2 hg
      · exact (hH0 g).1 hg
    rw [hcl]
    rfl
  have hK0 : ∀ g, g ∈ P.K0 ↔ c.grp g ∈ S.K0 := by
    have hX : ∀ g, (g ∈ P.St ∧ ∀ (a : Fin r) (b : Fin (r + 1)),
        H.h (g (P.A.f b)) (P.A.es a) ∈ M.L.O ∧ H.h (g (P.B.f b)) (P.B.es a) ∈ M.L.O) ↔
        c.grp g ∈ S.K0 := by
      intro g
      have hA : ∀ a b, H.h (g (P.A.f b)) (P.A.es a) = _root_.GlobalTheory.HL.hf M.L S.Hm
          (c.grp g (S.f b)) (S.es a) := by
        intro a b
        rw [c.f_eq, c.es_eq, hconj, ← hS, c.h_eq]
      have hB : ∀ a b, H.h (g (P.B.f b)) (P.B.es a) = _root_.GlobalTheory.HL.hf M.L S.Hm
          (c.grp g (S.f' b)) (S.es' a) := by
        intro a b
        rw [c.f'_eq, c.es'_eq, hconj, ← hS,
          c.h_eq]
      unfold _root_.GlobalTheory.HL.Frames.K0
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hSt]
      constructor
      · rintro ⟨hst, hint⟩
        have hst' := hst
        unfold _root_.GlobalTheory.HL.Frames.St at hst'
        rw [Subgroup.mem_inf] at hst'
        refine ⟨⟨hst, (unipotent_pairing_integral_iff_mem_stabilizer_lemma S S.f S.es S.T
          S.gram S.dual _ hst'.1).1 fun a b ↦ ?_⟩,
          (unipotent_pairing_integral_iff_mem_stabilizer_lemma S S.f' S.es' S.T'
          S.gram' S.dual' _ hst'.2).1 fun a b ↦ ?_⟩
        · rw [← hA]
          exact (hint a b).1
        · rw [← hB]
          exact (hint a b).2
      · rintro ⟨⟨hst, h1⟩, h2⟩
        have hst' := hst
        unfold _root_.GlobalTheory.HL.Frames.St at hst'
        rw [Subgroup.mem_inf] at hst'
        refine ⟨hst, fun a b ↦ ⟨?_, ?_⟩⟩
        · rw [hA]
          exact (unipotent_pairing_integral_iff_mem_stabilizer_lemma S S.f S.es S.T
            S.gram S.dual _ hst'.1).2 h1 a b
        · rw [hB]
          exact (unipotent_pairing_integral_iff_mem_stabilizer_lemma S S.f' S.es' S.T'
            S.gram' S.dual' _ hst'.2).2 h2 a b
    intro g
    have hcl : P.K0 = S.K0.comap c.grp.toMonoidHom := by
      unfold _root_.Formalism.MainNotions.S.LocNG.FPair.K0
      refine le_antisymm ((Subgroup.closure_le _).2 fun g hg ↦ ?_)
        (fun g hg ↦ Subgroup.subset_closure ?_)
      · exact (hX g).1 hg
      · exact (hX g).2 hg
    rw [hcl]
    rfl
  have hrel : ∀ A B : Subgroup S.GLV,
      (A.comap c.grp.toMonoidHom).relIndex
        (B.comap c.grp.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective c.grp.surjective]
  refine ⟨hUW0, hK0, ⟨hinj, hsurj⟩, hequiv, hAut, fun t ↦ ?_⟩
  have h1 : P.St ⊓ _root_.Formalism.MainNotions.S.LocNG.Aut t.abelian₂ =
      (S.St ⊓ MulAction.stabilizer S.GLV (c.lat t.abelian₂)).comap
        c.grp.toMonoidHom := by
    ext g
    rw [Subgroup.mem_inf, hSt, hAut]
    rfl
  have h2 : P.K0 = S.K0.comap c.grp.toMonoidHom := by
    ext g
    exact hK0 g
  unfold _root_.Formalism.MainNotions.S.LocNG.mu _root_.GlobalTheory.HL.Frames.mu _root_.Formalism.MainNotions.S.LocNG.volRel _root_.GlobalTheory.HL.invVol
  rw [h1, h2, hrel, hrel, one_div_div]
end _root_.GlobalTheory.HL.CoordMass
end GlobalTheory.HL.CoordMass

-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:39.847466+00:00
-- url     : https://prove2.me/submissions/aa3f3478-685c-4fe9-8a5a-6b62cd7714ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
namespace GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem grp_apply_e (g : V ≃ₗ[E] V) (v : V) :
    c.grp g (c.e v) = c.e (g v) := by
  show c.e (g (c.e.symm (c.e v))) = _
  simp
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem mapsTo_and_sub_mem_bot_of_fixes {W : Type} [AddCommGroup W] [Module E W] (T : W ≃ₗ[E] W)
    (N : Submodule E W) (hN : ∀ v ∈ N, T v = v) :
    (∀ v, T v ∈ N ↔ v ∈ N) ∧ ∀ v ∈ N, T v - v ∈ (⊥ : Submodule E W) := by
  refine ⟨fun v => ⟨fun h => ?_, fun h => by rwa [hN v h]⟩, fun v hv => ?_⟩
  · have h2 := T.injective (hN _ h)
    rwa [h2] at h
  · rw [hN v hv, sub_self]
    exact zero_mem _
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem isometry_fixing_frames_iff_grp_mem_H0 (g : V ≃ₗ[E] V) :
    ((∀ x y, H.h (g x) (g y) = H.h x y) ∧
      ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b) ↔
      c.grp g ∈ S.H0 := by
  have hT := grp_apply_e c g
  simp only [_root_.GlobalTheory.HL.Frames.H0, Subgroup.mem_inf]
  unfold _root_.GlobalTheory.HL.isomG _root_.GlobalTheory.HL.unipOn _root_.GlobalTheory.HL.Frames.ME
    _root_.GlobalTheory.HL.Frames.spanTo
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hiso, hfix⟩
    refine ⟨fun x y => ?_, mapsTo_and_sub_mem_bot_of_fixes _ _ ?_⟩
    · obtain ⟨x, rfl⟩ := c.e.surjective x
      obtain ⟨y, rfl⟩ := c.e.surjective y
      rw [hT, hT]
      exact (c.h_eq _ _).trans ((hiso x y).trans (c.h_eq x y).symm)
    · suffices h : _ ≤ LinearMap.eqLocus (c.grp g : S.V →ₗ[E] S.V)
          LinearMap.id from fun v hv => h hv
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) <;>
        rintro _ ⟨i, -, rfl⟩ <;>
        simp only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearEquiv.coe_coe, LinearMap.id_apply,
          c.f_eq, c.f'_eq, hT, (hfix i).1, (hfix i).2]
  · rintro ⟨hiso, hun⟩
    refine ⟨fun x y => ?_, fun b => ⟨?_, ?_⟩⟩
    · have h := hiso (c.e x) (c.e y)
      rw [hT, hT] at h
      rw [← c.h_eq (g x) (g y), ← c.h_eq x y]
      exact h
    · have h := hun.2 _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.isLt, rfl⟩))
      rw [Submodule.mem_bot, sub_eq_zero, c.f_eq, hT] at h
      exact c.e.injective h
    · have h := hun.2 _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.isLt, rfl⟩))
      rw [Submodule.mem_bot, sub_eq_zero, c.f'_eq, hT] at h
      exact c.e.injective h
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem mem_UW0_iff_grp_mem_H0 (g : V ≃ₗ[E] V) :
    g ∈ P.UW0 ↔ c.grp g ∈ S.H0 := by
  constructor
  · intro hg
    have hle : P.UW0 ≤
        S.H0.comap c.grp.toMonoidHom := by
      unfold _root_.Formalism.MainNotions.S.LocNG.FPair.UW0
      rw [Subgroup.closure_le]
      intro x hx
      exact (isometry_fixing_frames_iff_grp_mem_H0 c x).1 ⟨hx.1, hx.2⟩
    exact hle hg
  · intro hg
    unfold _root_.Formalism.MainNotions.S.LocNG.FPair.UW0
    apply Subgroup.subset_closure
    have h := (isometry_fixing_frames_iff_grp_mem_H0 c g).2 hg
    exact ⟨h.1, h.2⟩
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem apply_mem_perp_X_iff_of_isometry_fixing (g : V ≃ₗ[E] V) (hiso : ∀ x y, H.h (g x) (g y) = H.h x y)
    (f : Fin (r + 1) → V) (hf : ∀ b, g (f b) = f b) (v : V) :
    g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f) := by
  have hX : ∀ x ∈ H.X f, g x = x := by
    have h : H.X f ≤ LinearMap.eqLocus (g : V →ₗ[E] V) LinearMap.id := by
      unfold _root_.Formalism.MainNotions.S.Loc.HermSp.X
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearEquiv.coe_coe,
        LinearMap.id_apply, hf]
    exact fun x hx => h hx
  unfold _root_.Formalism.MainNotions.S.Loc.HermSp.perp
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine forall₂_congr fun x hx => ?_
  rw [← hiso v x, hX x hx]
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem image_setOf_subtype_eq_iff {X : Type} (g : X ≃ X) (K : X → Prop)
    (hK : ∀ v, K (g v) ↔ K v) (p q : {v // K v} → Prop) :
    g '' {v | ∃ h : K v, p ⟨v, h⟩} = {v | ∃ h : K v, q ⟨v, h⟩} ↔
      ∀ x y : {v // K v}, (y : X) = g x → (p x ↔ q y) := by
  constructor
  · intro hs x y hxy
    constructor
    · intro hp
      have hmem : (g x : X) ∈ g '' {v | ∃ h : K v, p ⟨v, h⟩} := ⟨x, ⟨x.2, hp⟩, rfl⟩
      rw [hs] at hmem
      obtain ⟨h, hq⟩ := hmem
      have hy : y = ⟨g x, h⟩ := Subtype.ext hxy
      rwa [hy]
    · intro hq
      have hmem : (y : X) ∈ {v | ∃ h : K v, q ⟨v, h⟩} := ⟨y.2, hq⟩
      rw [← hs] at hmem
      obtain ⟨w, ⟨hw, hpw⟩, hwy⟩ := hmem
      have hwx : w = x := g.injective (hwy.trans hxy)
      subst hwx
      exact hpw
  · intro h
    ext v
    constructor
    · rintro ⟨w, ⟨hw, hp⟩, rfl⟩
      exact ⟨(hK w).2 hw, (h ⟨w, hw⟩ ⟨g w, (hK w).2 hw⟩ rfl).1 hp⟩
    · rintro ⟨hv, hq⟩
      have hw : K (g.symm v) := by
        rw [← hK]
        simpa using hv
      exact ⟨g.symm v, ⟨hw, (h ⟨g.symm v, hw⟩ ⟨v, hv⟩ (by simp)).2 hq⟩, by simp⟩
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem grp_smul_inn_eq_inn_iff (g : V ≃ₗ[E] V) (f : Fin (r + 1) → V)
    (hK : ∀ v, g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f))
    (L L' : Submodule M.L.O (H.Wb f)) :
    c.grp g • c.inn f L =
        c.inn f L' ↔
      ∀ x y : ↥(H.perp (H.X f)), (y : V) = g x → (H.mkW f x ∈ L ↔ H.mkW f y ∈ L') := by
  have hT := grp_apply_e c g
  have hc : ∀ N : Submodule M.L.O (H.Wb f), (c.inn f N : Set S.V) =
      c.e '' {v | ∃ h : v ∈ H.perp (H.X f), H.mkW f ⟨v, h⟩ ∈ N} := by
    intro N
    ext w
    simp only [_root_.GlobalTheory.HL.Coord.inn,
      _root_.GlobalTheory.HL.Coord.lat, SetLike.mem_coe, Submodule.mem_map,
      Submodule.mem_comap, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨z.2, hz⟩, rfl⟩
    · rintro ⟨v, ⟨h, hv⟩, rfl⟩
      exact ⟨v, ⟨⟨v, h⟩, hv, rfl⟩, rfl⟩
  rw [← SetLike.coe_set_eq, Submodule.coe_pointwise_smul, hc, hc, ← Set.image_smul,
    Set.image_image]
  rw [show (fun v => c.grp g • c.e v) =
      c.e ∘ g.toEquiv from funext fun v => by
        simp [LinearEquiv.smul_def, hT]]
  rw [Set.image_comp, (Set.image_injective.2 c.e.injective).eq_iff]
  exact image_setOf_subtype_eq_iff g.toEquiv (· ∈ H.perp (H.X f)) hK (fun x => H.mkW f x ∈ L)
    (fun y => H.mkW f y ∈ L')
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem graph_transport_iff_lemma_11 (g : V ≃ₗ[E] V)
    (hKB : ∀ v, g v ∈ H.perp (H.X P.B.f) ↔ v ∈ H.perp (H.X P.B.f))
    (hKA : ∀ v, g v ∈ H.perp (H.X P.A.f) ↔ v ∈ H.perp (H.X P.A.f)) (d d' : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    c.grp g • {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧ _root_.GlobalTheory.HL.CoordDatum.Q d x' x} =
      {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧
        _root_.GlobalTheory.HL.CoordDatum.Q d' x' x} ↔
      ∀ (x' y' : ↥(H.perp (H.X P.B.f))) (x y : ↥(H.perp (H.X P.A.f))), (y' : V) = g x' →
        (y : V) = g x → (_root_.GlobalTheory.HL.CoordDatum.Q d x' x ↔ _root_.GlobalTheory.HL.CoordDatum.Q d' y' y) := by
  have hT := grp_apply_e c g
  let K : V × V → Prop := fun v => v.1 ∈ H.perp (H.X P.B.f) ∧ v.2 ∈ H.perp (H.X P.A.f)
  have hZ : ∀ d : _root_.Formalism.MainNotions.S.LocNG.Datum P, {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧ _root_.GlobalTheory.HL.CoordDatum.Q d x' x} =
      Prod.map c.e c.e ''
        {v | ∃ h : K v, _root_.GlobalTheory.HL.CoordDatum.Q d ⟨v.1, h.1⟩ ⟨v.2, h.2⟩} := by
    intro d
    ext p
    constructor
    · rintro ⟨x', x, rfl, hq⟩
      exact ⟨((x' : V), (x : V)), ⟨⟨x'.2, x.2⟩, hq⟩, rfl⟩
    · rintro ⟨v, ⟨h, hq⟩, rfl⟩
      exact ⟨⟨v.1, h.1⟩, ⟨v.2, h.2⟩, rfl, hq⟩
  have hK : ∀ v, K (Equiv.prodCongr g.toEquiv g.toEquiv v) ↔ K v := fun v =>
    and_congr (hKB v.1) (hKA v.2)
  have hinj : Function.Injective (Prod.map c.e c.e) :=
    c.e.injective.prodMap c.e.injective
  rw [hZ, hZ, ← Set.image_smul, Set.image_image]
  rw [show (fun v => c.grp g • Prod.map c.e c.e v) =
      Prod.map c.e c.e ∘ Equiv.prodCongr g.toEquiv g.toEquiv from
      funext fun v => by
        obtain ⟨a, b⟩ := v
        simp [Prod.smul_mk, LinearEquiv.smul_def, hT]]
  rw [Set.image_comp, (Set.image_injective.2 hinj).eq_iff]
  refine (image_setOf_subtype_eq_iff _ K hK
    (fun v => _root_.GlobalTheory.HL.CoordDatum.Q d ⟨v.1.1, v.2.1⟩ ⟨v.1.2, v.2.2⟩)
    (fun v => _root_.GlobalTheory.HL.CoordDatum.Q d' ⟨v.1.1, v.2.1⟩ ⟨v.1.2, v.2.2⟩)).trans ?_
  constructor
  · intro h x' y' x y hy' hy
    exact h ⟨((x' : V), (x : V)), x'.2, x.2⟩ ⟨((y' : V), (y : V)), y'.2, y.2⟩ (Prod.ext hy' hy)
  · rintro h ⟨⟨a, b⟩, ha, hb⟩ ⟨⟨a', b'⟩, ha', hb'⟩ hy
    have hy2 := Prod.ext_iff.1 hy
    exact h ⟨a, ha⟩ ⟨a', ha'⟩ ⟨b, hb⟩ ⟨b', hb'⟩ hy2.1 hy2.2
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem Datum_moves_iff_grp_smul_dat_eq (g : V ≃ₗ[E] V) (hg : g ∈ P.UW0) (d d' : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d' ↔
      c.grp g • c.dat d = c.dat d' := by
  obtain ⟨hiso, hfix⟩ := (isometry_fixing_frames_iff_grp_mem_H0 c g).2 ((mem_UW0_iff_grp_mem_H0 c g).1 hg)
  have hKA := apply_mem_perp_X_iff_of_isometry_fixing g hiso P.A.f (fun b => (hfix b).1)
  have hKB := apply_mem_perp_X_iff_of_isometry_fixing g hiso P.B.f (fun b => (hfix b).2)
  have hdat : ∀ d : _root_.Formalism.MainNotions.S.LocNG.Datum P, c.dat d =
      (c.inn P.A.f d.L, c.inn P.B.f d.L',
        {p : S.V × S.V | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))),
          p = (c.e x', c.e x) ∧
          _root_.GlobalTheory.HL.CoordDatum.Q d x' x}) := fun _ => rfl
  unfold _root_.Formalism.MainNotions.S.LocNG.Datum.Moves
  rw [hdat, hdat, Prod.smul_mk, Prod.smul_mk, Prod.mk.injEq, Prod.mk.injEq,
    grp_smul_inn_eq_inn_iff c g _ hKA, grp_smul_inn_eq_inn_iff c g _ hKB,
    graph_transport_iff_lemma_11 c g hKB hKA]
  refine and_congr_right fun c1 => and_congr_right fun c2 => ?_
  rcases hs : M.split with _ | s
  · have e1 := d.6 hs
    have e2 := d'.6 hs
    constructor
    · intro _ x' y' x y hy' hy
      simp only [_root_.GlobalTheory.HL.CoordDatum.Q, hs, e1, e2, Set.mem_empty_iff_false, or_false,
        true_and]
      exact and_congr (c2 x' y' hy') (c1 x y hy)
    · intro _ x' y' x y _ _
      simp only [e1, e2, Set.mem_empty_iff_false]
  · simp only [_root_.GlobalTheory.HL.CoordDatum.Q, hs, reduceCtorEq, false_and, false_or]
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem mkW_surjective (f : Fin (r + 1) → V) : Function.Surjective (H.mkW f) := by
  unfold _root_.Formalism.MainNotions.S.Loc.HermSp.mkW
  exact Submodule.mkQ_surjective _
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem dat_injective : Function.Injective c.dat := by
  intro d d' hdd
  have hm := (Datum_moves_iff_grp_smul_dat_eq c 1 (one_mem _) d d').2 (by rw [map_one, one_smul]; exact hdd)
  obtain ⟨h1, h2, h3⟩ := hm
  obtain ⟨L, L', hL, hL', io, hio⟩ := d
  obtain ⟨N, N', hN, hN', jo, hjo⟩ := d'
  have hLN : L = N := by
    ext w
    obtain ⟨x, rfl⟩ := mkW_surjective P.A.f w
    exact h1 x x rfl
  have hLN' : L' = N' := by
    ext w
    obtain ⟨x, rfl⟩ := mkW_surjective P.B.f w
    exact h2 x x rfl
  have hio' : io = jo := by
    ext ⟨a, b⟩
    obtain ⟨x', rfl⟩ := mkW_surjective P.B.f a
    obtain ⟨x, rfl⟩ := mkW_surjective P.A.f b
    exact h3 x' x' x x rfl rfl
  subst hLN hLN' hio'
  rfl
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem Datum_rel_iff_exists_H0_smul_dat_eq (d d' : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    _root_.Formalism.MainNotions.S.LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0,
      h • c.dat d = c.dat d' := by
  unfold _root_.Formalism.MainNotions.S.LocNG.Datum.Rel
  constructor
  · rintro ⟨g, hg, hm⟩
    exact ⟨_, (mem_UW0_iff_grp_mem_H0 c g).1 hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d').1 hm⟩
  · rintro ⟨h, hh, he⟩
    obtain ⟨g, rfl⟩ := c.grp.surjective h
    have hg := (mem_UW0_iff_grp_mem_H0 c g).2 hh
    exact ⟨g, hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d').2 he⟩
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem Datum_stab_eq_comap_H0_inf_stabilizer (d : _root_.Formalism.MainNotions.S.LocNG.Datum P) :
    _root_.Formalism.MainNotions.S.LocNG.Datum.Stab d = (S.H0 ⊓
      MulAction.stabilizer S.GLV (c.dat d)).comap
        c.grp.toMonoidHom := by
  unfold _root_.Formalism.MainNotions.S.LocNG.Datum.Stab
  have hset : {g | g ∈ P.UW0 ∧ _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d} =
      ((S.H0 ⊓ MulAction.stabilizer S.GLV
        (c.dat d)).comap c.grp.toMonoidHom :
          Set (V ≃ₗ[E] V)) := by
    ext g
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨hg, hm⟩
      exact ⟨(mem_UW0_iff_grp_mem_H0 c g).1 hg, (Datum_moves_iff_grp_smul_dat_eq c g hg d d).1 hm⟩
    · rintro ⟨hg, hs⟩
      have hg' := (mem_UW0_iff_grp_mem_H0 c g).2 hg
      exact ⟨hg', (Datum_moves_iff_grp_smul_dat_eq c g hg' d d).2 hs⟩
  rw [hset, Subgroup.closure_eq]
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} in
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S) in
private theorem relIndex_comap_mulEquiv {G G' : Type} [Group G] [Group G'] (f : G ≃* G')
    (A B : Subgroup G') :
    (A.comap f.toMonoidHom).relIndex (B.comap f.toMonoidHom) = A.relIndex B := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective f.surjective]
end GlobalTheory.HL.CoordDatum
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
open ValuativeRel
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}
variable {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k}
  (c : _root_.GlobalTheory.HL.Coord P S)
namespace GlobalTheory.HL.CoordDatum
namespace _root_.GlobalTheory.HL.CoordDatum
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k)
    (c : _root_.GlobalTheory.HL.Coord P S), Function.Injective c.dat ∧
    (∀ g ∈ P.UW0, ∀ d d', _root_.Formalism.MainNotions.S.LocNG.Datum.Moves g d d' ↔
      c.grp g • c.dat d = c.dat d') ∧
    (∀ d d', _root_.Formalism.MainNotions.S.LocNG.Datum.Rel d d' ↔
      ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧
    (∀ d g, g ∈ _root_.Formalism.MainNotions.S.LocNG.Datum.Stab d ↔ c.grp g ∈
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧
    ∀ d0 d, _root_.Formalism.MainNotions.S.LocNG.Datum.wt d0 d = _root_.GlobalTheory.HL.invVol
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0))
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c
  refine ⟨dat_injective c, fun g hg d d' => Datum_moves_iff_grp_smul_dat_eq c g hg d d',
    fun d d' => Datum_rel_iff_exists_H0_smul_dat_eq c d d', fun d g => ?_, fun d0 d => ?_⟩
  · rw [Datum_stab_eq_comap_H0_inf_stabilizer c d]
    exact Subgroup.mem_comap
  · unfold _root_.Formalism.MainNotions.S.LocNG.Datum.wt _root_.Formalism.MainNotions.S.LocNG.volRel _root_.GlobalTheory.HL.invVol
    rw [Datum_stab_eq_comap_H0_inf_stabilizer c d, Datum_stab_eq_comap_H0_inf_stabilizer c d0, relIndex_comap_mulEquiv, relIndex_comap_mulEquiv,
      one_div_div]
end _root_.GlobalTheory.HL.CoordDatum
end GlobalTheory.HL.CoordDatum

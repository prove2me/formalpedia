-- Prove2me | solution 1 for IsRegularLocalRing.spanFinrank_ker_add_ringKrullDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e4e25e92-a376-55f6-9d6c-82098ff8698b

import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing

noncomputable section

namespace RSMU

section CotImage

variable {A : Type*} [CommRing A] [IsLocalRing A]

def cotImage (K : Ideal A) : Submodule (ResidueField A) (CotangentSpace A) :=
  Submodule.span (ResidueField A)
    ((maximalIdeal A).toCotangent '' {m : ↥(maximalIdeal A) | (m : A) ∈ K})

theorem toCotangent_mem_cotImage {K : Ideal A} (m : ↥(maximalIdeal A)) (hm : (m : A) ∈ K) :
    (maximalIdeal A).toCotangent m ∈ cotImage K :=
  Submodule.subset_span ⟨m, hm, rfl⟩

theorem cotImage_mono {K K' : Ideal A} (h : K ≤ K') : cotImage K ≤ cotImage K' := by
  apply Submodule.span_mono
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, h hm, rfl⟩

theorem residue_smul_eq (c : A) (w : CotangentSpace A) : (residue A c) • w = c • w := by
  show (algebraMap A (ResidueField A) c) • w = c • w
  exact algebraMap_smul _ c w

theorem exists_eq_toCotangent_of_mem_cotImage {K : Ideal A} {w : CotangentSpace A} (hw : w ∈ cotImage K) :
    ∃ m : ↥(maximalIdeal A), (m : A) ∈ K ∧ (maximalIdeal A).toCotangent m = w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨m, hm, rfl⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨m', hm', rfl⟩ := hy
    exact ⟨m + m', K.add_mem hm hm', by simp⟩
  | smul c x _ hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c • m, ?_, ?_⟩
    · rw [Submodule.coe_smul, smul_eq_mul]; exact K.mul_mem_left c hm
    · rw [map_smul]
      exact (residue_smul_eq c _).symm

def cotSpan {ι : Type*} (z : ι → ↥(maximalIdeal A)) : Submodule (ResidueField A) (CotangentSpace A) :=
  Submodule.span (ResidueField A) (Set.range fun i => (maximalIdeal A).toCotangent (z i))

def idealSpan {ι : Type*} (z : ι → ↥(maximalIdeal A)) : Ideal A := Ideal.span (Set.range fun i => (z i : A))

theorem idealSpan_le {ι : Type*} (z : ι → ↥(maximalIdeal A)) : idealSpan z ≤ maximalIdeal A := by
  rw [idealSpan, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact (z i).2

theorem exists_eq_toCotangent_of_mem_cotSpan {ι : Type*} {z : ι → ↥(maximalIdeal A)} {u : CotangentSpace A}
    (hu : u ∈ cotSpan z) :
    ∃ y : ↥(maximalIdeal A), (y : A) ∈ idealSpan z ∧ (maximalIdeal A).toCotangent y = u := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨z i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, (idealSpan z).add_mem ha hb, by simp⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c • a, ?_, ?_⟩
    · rw [Submodule.coe_smul, smul_eq_mul]; exact (idealSpan z).mul_mem_left c ha
    · rw [map_smul]; exact (residue_smul_eq c _).symm

theorem cotSpan_sup_cotImage_eq_top {ι : Type*} (z : ι → ↥(maximalIdeal A)) (K : Ideal A)
    (h : maximalIdeal A ≤ idealSpan z ⊔ K) : cotSpan z ⊔ cotImage K = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  obtain ⟨m, rfl⟩ := (maximalIdeal A).toCotangent_surjective w
  have hm : (m : A) ∈ idealSpan z ⊔ K := h m.2
  rw [Submodule.mem_sup] at hm
  obtain ⟨y, hy, kk, hk, hyk⟩ := hm
  have hy𝔪 : y ∈ maximalIdeal A := idealSpan_le z hy
  have hk𝔪 : kk ∈ maximalIdeal A := by
    have : kk = m - y := by rw [← hyk]; ring
    rw [this]; exact (maximalIdeal A).sub_mem m.2 hy𝔪
  have hsplit : m = ⟨y, hy𝔪⟩ + ⟨kk, hk𝔪⟩ := Subtype.ext hyk.symm
  rw [hsplit, map_add]
  refine Submodule.add_mem_sup ?_ (toCotangent_mem_cotImage _ hk)

  have hy' : (⟨y, hy𝔪⟩ : ↥(maximalIdeal A)) ∈ Submodule.span A (Set.range z) := by
    have hmap : Submodule.map (maximalIdeal A).subtype (Submodule.span A (Set.range z)) = idealSpan z := by
      rw [Submodule.map_span, idealSpan, ← Set.range_comp]
      rfl
    have : y ∈ Submodule.map (maximalIdeal A).subtype (Submodule.span A (Set.range z)) := by rw [hmap]; exact hy
    obtain ⟨y', hy', hyy'⟩ := Submodule.mem_map.mp this
    have : y' = ⟨y, hy𝔪⟩ := Subtype.ext hyy'
    rw [← this]; exact hy'
  have hmap2 : Submodule.map (maximalIdeal A).toCotangent (Submodule.span A (Set.range z)) ≤
      (cotSpan z).restrictScalars A := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hmap2 (Submodule.mem_map_of_mem hy')

theorem le_idealSpan_sup_of_cotSpan_sup_cotImage_eq_top [IsNoetherianRing A] {ι : Type*}
    (z : ι → ↥(maximalIdeal A)) (K : Ideal A) (h : cotSpan z ⊔ cotImage K = ⊤) :
    maximalIdeal A ≤ idealSpan z ⊔ K := by

  have h1 : (maximalIdeal A : Submodule A A) ≤ (idealSpan z ⊔ K) ⊔ maximalIdeal A • maximalIdeal A := by
    intro m hm
    have hw : (maximalIdeal A).toCotangent ⟨m, hm⟩ ∈ cotSpan z ⊔ cotImage K := by rw [h]; trivial
    rw [Submodule.mem_sup] at hw
    obtain ⟨u, hu, w, hw, huw⟩ := hw
    obtain ⟨mk, hmkK, rfl⟩ := exists_eq_toCotangent_of_mem_cotImage hw
    obtain ⟨y, hy, rfl⟩ := exists_eq_toCotangent_of_mem_cotSpan hu

    have hdiff : (maximalIdeal A).toCotangent (⟨m, hm⟩ - y - mk) = 0 := by
      rw [map_sub, map_sub, ← huw]; abel
    rw [Ideal.toCotangent_eq_zero] at hdiff
    have hsq : ((⟨m, hm⟩ - y - mk : ↥(maximalIdeal A)) : A) ∈ maximalIdeal A • maximalIdeal A := by
      rw [Submodule.coe_sub, Submodule.coe_sub] at hdiff ⊢
      simpa [sq, Ideal.smul_eq_mul] using hdiff
    have : m = ((y : A) + (mk : A)) + ((⟨m, hm⟩ - y - mk : ↥(maximalIdeal A)) : A) := by
      simp only [Submodule.coe_sub]; ring
    rw [this]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hy hmkK) hsq

  have hfg : (maximalIdeal A : Submodule A A).FG := IsNoetherian.noetherian _
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson ⊥) h1

end CotImage

section Helpers

variable {R : Type*} [CommRing R]

theorem spanFinrank_span_finset_le {M : Type*} [AddCommGroup M] [Module R M] (s : Finset M) :
    (Submodule.span R (s : Set M)).spanFinrank ≤ s.card := by
  have h : (Submodule.span R (s : Set M)).spanRank ≤ s.card := by
    simpa using Submodule.spanRank_span_le_card (R := R) (s : Set M)
  have h__af := Cardinal.toNat_le_toNat h (Cardinal.natCast_lt_aleph0 (n := s.card))
  simp at h__af
  exact h__af

theorem spanFinrank_span_range_le {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} (v : Fin n → M) :
    (Submodule.span R (Set.range v)).spanFinrank ≤ n := by
  classical
  have hr : Set.range v = ((Finset.univ.image v : Finset M) : Set M) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hr]
  exact (spanFinrank_span_finset_le _).trans (Finset.card_image_le.trans (by simp))

theorem ringKrullDim_eq_natCast_iff [IsLocalRing R] (n : ℕ) :
    ringKrullDim R = n ↔ (maximalIdeal R).height = n := by
  rw [← maximalIdeal_height_eq_ringKrullDim]
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]; rfl

theorem ringKrullDim_le_natCast_iff [IsLocalRing R] (n : ℕ) :
    ringKrullDim R ≤ n ↔ (maximalIdeal R).height ≤ n := by
  rw [← maximalIdeal_height_eq_ringKrullDim]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem natCast_le_ringKrullDim_iff [IsLocalRing R] (n : ℕ) :
    (n : WithBot ℕ∞) ≤ ringKrullDim R ↔ (n : ℕ∞) ≤ (maximalIdeal R).height := by
  rw [← maximalIdeal_height_eq_ringKrullDim]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

end Helpers

section Surjection

variable {A C : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing C] [IsLocalRing C]
  (g : A →+* C) (hg : Function.Surjective g)

include hg

theorem mem_maximalIdeal_of_map_mem {a : A} (ha : g a ∈ maximalIdeal C) : a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  exact fun h => ha (h.map g)

theorem maximalIdeal_le_idealSpan_sup_ker {ι : Type*} (z : ι → ↥(maximalIdeal A))
    (h : maximalIdeal C ≤ Ideal.span (Set.range fun i => g (z i))) :
    maximalIdeal A ≤ idealSpan z ⊔ RingHom.ker g := by
  intro m hm
  have hgm : g m ∈ maximalIdeal C := by
    rw [← map_maximalIdeal_of_surjective g hg]; exact Ideal.mem_map_of_mem g hm
  have hspan : Ideal.span (Set.range fun i => g (z i)) = Ideal.map g (idealSpan z) := by
    rw [idealSpan, Ideal.map_span, ← Set.range_comp]; rfl
  have := h hgm
  rw [hspan, Ideal.mem_map_iff_of_surjective g hg] at this
  obtain ⟨y, hy, hgy⟩ := this
  have : m = y + (m - y) := by ring
  rw [this]
  refine Submodule.add_mem_sup hy ?_
  rw [RingHom.mem_ker, map_sub, hgy, sub_self]

theorem finrank_quotient_cotImage_le :
    Module.finrank (ResidueField A) (CotangentSpace A ⧸ cotImage (RingHom.ker g)) ≤
      (maximalIdeal C).spanFinrank := by

  have hfgC : (maximalIdeal C).FG := by
    rw [← map_maximalIdeal_of_surjective g hg]; exact Ideal.FG.map (IsNoetherian.noetherian (maximalIdeal A)) g
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfgC
  have hsfin : s.Finite := Set.finite_of_encard_eq_coe hs
  haveI := hsfin.fintype
  have hcard : Fintype.card s = (maximalIdeal C).spanFinrank := by
    have := Set.encard_eq_coe_toFinset_card s
    rw [hs] at this
    rw [← Set.toFinset_card]
    exact_mod_cast this.symm

  have hs𝔪 : ∀ c : s, Function.surjInv hg c ∈ maximalIdeal A := fun c =>
    mem_maximalIdeal_of_map_mem g hg (by
      rw [Function.surjInv_eq hg]
      have : (c : C) ∈ Submodule.span C s := Submodule.subset_span c.2
      rw [hspan] at this; exact this)
  let z : s → ↥(maximalIdeal A) := fun c => ⟨Function.surjInv hg c, hs𝔪 c⟩
  have hz : maximalIdeal C ≤ Ideal.span (Set.range fun i => g (z i)) := by
    have : (Set.range fun i => g (z i)) = s := by
      ext c; constructor
      · rintro ⟨i, rfl⟩; show g (Function.surjInv hg i) ∈ s; rw [Function.surjInv_eq hg]; exact i.2
      · intro hc; exact ⟨⟨c, hc⟩, Function.surjInv_eq hg c⟩
    rw [this]
    show maximalIdeal C ≤ Submodule.span C s
    rw [hspan]
  have htop := cotSpan_sup_cotImage_eq_top z (RingHom.ker g) (maximalIdeal_le_idealSpan_sup_ker g hg z hz)

  have hmap : Submodule.map (cotImage (RingHom.ker g)).mkQ (cotSpan z) = ⊤ := by
    rw [Submodule.map_mkQ_eq_top, sup_comm]; exact htop
  calc Module.finrank (ResidueField A) (CotangentSpace A ⧸ cotImage (RingHom.ker g))
      = Module.finrank (ResidueField A)
          (⊤ : Submodule (ResidueField A) (CotangentSpace A ⧸ cotImage (RingHom.ker g))) :=
        (finrank_top _ _).symm
    _ = Module.finrank (ResidueField A) (Submodule.map (cotImage (RingHom.ker g)).mkQ (cotSpan z)) := by
        rw [hmap]
    _ ≤ Module.finrank (ResidueField A) (cotSpan z) := Submodule.finrank_map_le _ _
    _ ≤ Fintype.card s := finrank_range_le_card _
    _ = (maximalIdeal C).spanFinrank := hcard

theorem spanFinrank_maximalIdeal_le_finrank_quotient_cotImage :
    (maximalIdeal C).spanFinrank ≤
      Module.finrank (ResidueField A) (CotangentSpace A ⧸ cotImage (RingHom.ker g)) := by
  set W := cotImage (RingHom.ker g) with hW
  set t := Module.finrank (ResidueField A) (CotangentSpace A ⧸ W) with ht
  let bQ := Module.finBasis (ResidueField A) (CotangentSpace A ⧸ W)

  have hlift : ∀ i : Fin t, ∃ m : ↥(maximalIdeal A), W.mkQ ((maximalIdeal A).toCotangent m) = bQ i := by
    intro i
    obtain ⟨v, hv⟩ := W.mkQ_surjective (bQ i)
    obtain ⟨m, rfl⟩ := (maximalIdeal A).toCotangent_surjective v
    exact ⟨m, hv⟩
  choose m hm using hlift
  have hmap : Submodule.map W.mkQ (cotSpan m) = ⊤ := by
    rw [cotSpan, Submodule.map_span, ← Set.range_comp]
    have : (W.mkQ ∘ fun i => (maximalIdeal A).toCotangent (m i)) = bQ := by
      funext i; exact hm i
    rw [this, bQ.span_eq]
  have htop : cotSpan m ⊔ W = ⊤ := by
    rw [sup_comm, ← Submodule.map_mkQ_eq_top]; exact hmap
  have hle := le_idealSpan_sup_of_cotSpan_sup_cotImage_eq_top m (RingHom.ker g) htop

  have hC : maximalIdeal C = Ideal.span (Set.range fun i => g (m i)) := by
    apply le_antisymm
    · rw [← map_maximalIdeal_of_surjective g hg]
      refine (Ideal.map_mono hle).trans ?_
      rw [Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker g).mpr le_rfl, sup_bot_eq, idealSpan, Ideal.map_span,
        ← Set.range_comp]
      rfl
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [← map_maximalIdeal_of_surjective g hg]
      exact Ideal.mem_map_of_mem g (m i).2
  rw [hC]
  exact spanFinrank_span_range_le _

theorem spanFinrank_maximalIdeal_eq_finrank_quotient_cotImage :
    (maximalIdeal C).spanFinrank =
      Module.finrank (ResidueField A) (CotangentSpace A ⧸ cotImage (RingHom.ker g)) :=
  le_antisymm (spanFinrank_maximalIdeal_le_finrank_quotient_cotImage g hg) (finrank_quotient_cotImage_le g hg)

end Surjection

section Main

theorem main {A B : Type*} [CommRing A] [CommRing B] [IsRegularLocalRing A] [IsRegularLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    ((RingHom.ker f).spanFinrank : WithBot ℕ∞) + ringKrullDim B = ringKrullDim A := by
  classical
  set I := RingHom.ker f with hI
  set a := (maximalIdeal A).spanFinrank with ha
  set b := (maximalIdeal B).spanFinrank with hb
  have hdimA : ringKrullDim A = a := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hdimB : ringKrullDim B = b := IsRegularLocalRing.spanFinrank_maximalIdeal.symm

  set W := cotImage I with hW
  have hfinV : Module.finrank (ResidueField A) (CotangentSpace A) = a :=
    (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace A).symm
  have hL1 : b = Module.finrank (ResidueField A) (CotangentSpace A ⧸ W) :=
    spanFinrank_maximalIdeal_eq_finrank_quotient_cotImage f hf
  set s := Module.finrank (ResidueField A) W with hs
  have hsab : s + b = a := by
    rw [hL1, ← hfinV, add_comm]; exact Submodule.finrank_quotient_add_finrank W

  let bW := Module.finBasis (ResidueField A) W
  have hx : ∀ i : Fin s, ∃ m : ↥(maximalIdeal A), (m : A) ∈ I ∧ (maximalIdeal A).toCotangent m = (bW i : _) :=
    fun i => exists_eq_toCotangent_of_mem_cotImage (bW i).2
  choose x hxI hxcot using hx
  set J := idealSpan x with hJ
  have hJI : J ≤ I := by
    rw [hJ, idealSpan, Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hxI i
  have hJ𝔪 : J ≤ maximalIdeal A := idealSpan_le x
  have hJtop : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hJ𝔪))
  have hWJ : cotImage J = W := by
    refine le_antisymm (cotImage_mono hJI) ?_
    intro w hw
    have hmem : (⟨w, hw⟩ : W) ∈ Submodule.span (ResidueField A) (Set.range bW) := by
      rw [bW.span_eq]; trivial
    have hmap : Submodule.map W.subtype (Submodule.span (ResidueField A) (Set.range bW)) ≤ cotImage J := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [Submodule.subtype_apply, ← hxcot i]
      exact toCotangent_mem_cotImage _ (Ideal.subset_span ⟨i, rfl⟩)
    exact hmap (Submodule.mem_map_of_mem hmem)

  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hμJ : (maximalIdeal (A ⧸ J)).spanFinrank = b := by
    rw [spanFinrank_maximalIdeal_eq_finrank_quotient_cotImage (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, hWJ, ← hL1]
  have hμJle : J.spanFinrank ≤ s := by
    rw [hJ, idealSpan]; exact spanFinrank_span_range_le _

  have hjacJ : J ≤ Ring.jacobson A := by rw [ringJacobson_eq_maximalIdeal]; exact hJ𝔪
  have hKrullJ := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank J hjacJ

  have hhJle : (maximalIdeal (A ⧸ J)).height ≤ b := by
    have := Ideal.height_le_spanFinrank (maximalIdeal (A ⧸ J)) (maximalIdeal.isMaximal _).ne_top
    rw [hμJ] at this; exact this
  have hhJ : (maximalIdeal (A ⧸ J)).height = b := by

    have h1 : ((a : ℕ∞) : WithBot ℕ∞) ≤ ((maximalIdeal (A ⧸ J)).height : WithBot ℕ∞) + (s : ℕ∞) := by
      have := hKrullJ
      rw [hdimA, ← maximalIdeal_height_eq_ringKrullDim] at this
      refine this.trans ?_
      exact add_le_add (le_refl _) (by exact_mod_cast hμJle)
    have h1' : (a : ℕ∞) ≤ (maximalIdeal (A ⧸ J)).height + s := by exact_mod_cast h1
    generalize hh : (maximalIdeal (A ⧸ J)).height = h at h1' hhJle ⊢
    induction h using ENat.recTopCoe with
    | top => simp at hhJle
    | coe m => norm_cast at h1' hhJle ⊢; omega
  have hdimJ : ringKrullDim (A ⧸ J) = b := (ringKrullDim_eq_natCast_iff b).mpr hhJ
  haveI : IsRegularLocalRing (A ⧸ J) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by rw [hμJ, hdimJ])
  haveI : IsDomain (A ⧸ J) := IsRegularLocalRing.isDomain _

  let gbar : A ⧸ J →+* B := Ideal.Quotient.lift J f (fun y hy => hJI hy)
  have hgbar_mk : ∀ y : A, gbar (Ideal.Quotient.mk J y) = f y := fun y => Ideal.Quotient.lift_mk _ _ _
  have hgbar : Function.Surjective gbar := by
    intro y; obtain ⟨z, rfl⟩ := hf y; exact ⟨Ideal.Quotient.mk J z, hgbar_mk z⟩
  have hK : RingHom.ker gbar = ⊥ := by
    by_contra hne
    obtain ⟨y, hyK, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hyreg : IsSMulRegular (A ⧸ J) y := IsSMulRegular.of_ne_zero hy0
    have hy𝔪 : y ∈ maximalIdeal (A ⧸ J) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map gbar
      rw [RingHom.mem_ker] at hyK
      rw [hyK] at this
      exact not_isUnit_zero this
    have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hyreg hy𝔪

    have hyle : Ideal.span {y} ≤ RingHom.ker gbar := by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hyK
    let g2 : (A ⧸ J) ⧸ Ideal.span {y} →+* B := Ideal.Quotient.lift _ gbar (fun z hz => hyle hz)
    have hg2 : Function.Surjective g2 := by
      intro w; obtain ⟨z, rfl⟩ := hgbar w; exact ⟨Ideal.Quotient.mk _ z, Ideal.Quotient.lift_mk _ _ _⟩
    have hle := ringKrullDim_le_of_surjective g2 hg2
    rw [hdimB] at hle

    have hytop : Ideal.span {y} ≠ ⊤ := fun h => (maximalIdeal.isMaximal _).ne_top
      (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy𝔪))))
    haveI : Nontrivial ((A ⧸ J) ⧸ Ideal.span {y}) := Ideal.Quotient.nontrivial_iff.mpr hytop
    haveI : IsLocalRing ((A ⧸ J) ⧸ Ideal.span {y}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    rw [hdimJ, ← maximalIdeal_height_eq_ringKrullDim] at hdrop
    rw [← maximalIdeal_height_eq_ringKrullDim] at hle
    have hle' : (b : ℕ∞) ≤ (maximalIdeal ((A ⧸ J) ⧸ Ideal.span {y})).height := by exact_mod_cast hle
    have hdrop' : (maximalIdeal ((A ⧸ J) ⧸ Ideal.span {y})).height + 1 = b := by exact_mod_cast hdrop
    generalize hh : (maximalIdeal ((A ⧸ J) ⧸ Ideal.span {y})).height = h at hle' hdrop'
    induction h using ENat.recTopCoe with
    | top => simp at hdrop'
    | coe m => norm_cast at hle' hdrop'; omega

  have hIJ : I ≤ J := by
    intro i hi
    have : Ideal.Quotient.mk J i ∈ RingHom.ker gbar := by
      rw [RingHom.mem_ker, hgbar_mk]; exact hi
    rw [hK, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hIeqJ : I = J := le_antisymm hIJ hJI
  have hμIle : I.spanFinrank ≤ s := hIeqJ ▸ hμJle

  have hjacI : I ≤ Ring.jacobson A := by rw [ringJacobson_eq_maximalIdeal, hIeqJ]; exact hJ𝔪
  have hKrullI := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I hjacI
  have hdimAI : ringKrullDim (A ⧸ I) = b := by
    rw [← hdimB]; exact RingEquiv.ringKrullDim (RingHom.quotientKerEquivOfSurjective hf)
  have hμIge : a ≤ b + I.spanFinrank := by
    rw [hdimA, hdimAI] at hKrullI
    have : ((a : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞) + (I.spanFinrank : ℕ∞) := hKrullI
    exact_mod_cast this
  have hμI : I.spanFinrank = a - b := by omega
  rw [hdimA, hdimB, hμI]
  have : a - b + b = a := by omega
  exact_mod_cast congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) this

end Main

end RSMU

end

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [IsRegularLocalRing A] [IsRegularLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    ((RingHom.ker f).spanFinrank : WithBot ℕ∞) + ringKrullDim B = ringKrullDim A :=
  RSMU.main f hf

end S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq
end P2MW
export P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq (solution)

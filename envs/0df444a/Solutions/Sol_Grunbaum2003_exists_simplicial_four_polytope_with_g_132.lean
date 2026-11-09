-- Prove2me | solution 1 for Grunbaum2003.exists_simplicial_four_polytope_with_g_132
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T04:39:12.339103+00:00
-- url     : https://prove2.me/submissions/a27c5ce5-8bdc-4121-aeb3-f7767151911f

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
open scoped BigOperators Classical

namespace GHard

/-- Any exposed face of a finite hull is the hull of its incident input points. -/
theorem finite_face_hull {d : ℕ} {ι : Type*} [Finite ι]
    (v : ι → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

/-- A linear support certificate realizes an exposed face and certifies its exact
input-label incidence set. -/
theorem finite_face_of_support {d : ℕ} {ι : Type*} [Finite ι]
    (v : ι → Fin d → ℝ) (s : Set (ι)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : ι, l (v i) ≤ b)
    (heq : ∀ i : ι, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : ι, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : ι, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          finite_face_hull v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

abbrev sign (b : Bool) : ℝ := if b then 1 else -1

def vertex {d : ℕ} (p : Fin d × Bool) : Fin d → ℝ := Pi.single p.1 (sign p.2)

def hull (d : ℕ) : Set (Fin d → ℝ) := convexHull ℝ (Set.range (@vertex d))

def compatible {d : ℕ} (I : Finset (Fin d × Bool)) : Prop :=
  ∀ i : Fin d, ¬ ((i, true) ∈ I ∧ (i, false) ∈ I)

instance {d : ℕ} (I : Finset (Fin d × Bool)) : Decidable (compatible I) :=
  Fintype.decidableForallFintype

lemma vertex_apply {d : ℕ} (p : Fin d × Bool) (j : Fin d) :
    vertex p j = if p.1 = j then sign p.2 else 0 := by
  simp [vertex, Pi.single_apply, eq_comm]

lemma sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> norm_num [sign]

lemma compatible_injective {d : ℕ} {I : Finset (Fin d × Bool)} (hI : compatible I) :
    Function.Injective (fun p : I => p.val.1) := by
  rintro ⟨⟨i, b⟩, hi⟩ ⟨⟨j, c⟩, hj⟩ hij
  dsimp at hij
  subst j
  apply Subtype.ext
  cases b <;> cases c <;> try rfl
  · exact False.elim (hI i ⟨hj, hi⟩)
  · exact False.elim (hI i ⟨hi, hj⟩)

lemma compatible_affineIndependent {d : ℕ} {I : Finset (Fin d × Bool)}
    (hI : compatible I) : AffineIndependent ℝ (fun p : I => vertex p.val) := by
  have hli := (Pi.basisFun ℝ (Fin d)).linearIndependent.comp
    (fun p : I => p.val.1) (compatible_injective hI)
  have hli' := hli.units_smul (fun p : I => Units.mk0 (sign p.val.2) (sign_ne_zero _))
  have heq : ((fun p : I => Units.mk0 (sign p.val.2) (sign_ne_zero _)) •
      (fun p : I => (Pi.basisFun ℝ (Fin d)) p.val.1)) = (fun p : I => vertex p.val) := by
    funext p j
    simp [Pi.basisFun_apply, vertex, Pi.single_apply]
  change LinearIndependent ℝ ((fun p : I => Units.mk0 (sign p.val.2) (sign_ne_zero _)) •
    (fun p : I => (Pi.basisFun ℝ (Fin d)) p.val.1)) at hli'
  rw [heq] at hli'
  exact hli'.affineIndependent

noncomputable def support {d : ℕ} (I : Finset (Fin d × Bool)) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin d, (if (j, true) ∈ I then 1 else if (j, false) ∈ I then -1 else 0 : ℝ) •
    ContinuousLinearMap.proj j

lemma support_vertex {d : ℕ} (I : Finset (Fin d × Bool)) (p : Fin d × Bool) :
    support I (vertex p) =
      (if (p.1, true) ∈ I then 1 else if (p.1, false) ∈ I then -1 else 0 : ℝ) * sign p.2 := by
  simp only [support, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, vertex_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma compatible_support {d : ℕ} {I : Finset (Fin d × Bool)} (hI : compatible I)
    (p : Fin d × Bool) : support I (vertex p) ≤ 1 ∧
      (support I (vertex p) = 1 ↔ p ∈ I) := by
  rcases p with ⟨i, b⟩
  rw [support_vertex]
  have hi := hI i
  by_cases ht : (i, true) ∈ I <;> by_cases hf : (i, false) ∈ I <;>
    cases b <;> simp_all [sign] <;> norm_num

lemma compatible_face {d : ℕ} {I : Finset (Fin d × Bool)}
    (hI : compatible I) (hne : I.Nonempty) :
    IsExposed ℝ (hull d) (convexHull ℝ (vertex '' (I : Set (Fin d × Bool)))) ∧
      ∀ p : Fin d × Bool, vertex p ∈ convexHull ℝ (vertex '' (I : Set (Fin d × Bool))) ↔ p ∈ I := by
  exact finite_face_of_support vertex (I : Set (Fin d × Bool)) hne
    (support I) 1 (fun p => (compatible_support hI p).1) (fun p => (compatible_support hI p).2)

lemma vertex_neg {d : ℕ} (p : Fin d × Bool) :
    vertex (p.1, !p.2) = -vertex p := by
  ext j
  rcases p with ⟨i, b⟩
  cases b <;> simp [vertex, sign, Pi.single_apply] <;> split_ifs <;> norm_num

lemma vertex_mem {d : ℕ} (p : Fin d × Bool) : vertex p ∈ hull d :=
  subset_convexHull ℝ _ (Set.mem_range_self p)

lemma hull_affineSpan (d : ℕ) (hd : 0 < d) : affineSpan ℝ (hull d) = ⊤ := by
  let A := affineSpan ℝ (hull d)
  have hv : ∀ p : Fin d × Bool, vertex p ∈ A :=
    fun p => mem_affineSpan ℝ (vertex_mem p)
  let i₀ : Fin d := ⟨0, hd⟩
  have hz : (0 : Fin d → ℝ) ∈ A := by
    have hm := A.smul_vsub_vadd_mem (1 / 2 : ℝ) (hv (i₀, true))
      (hv (i₀, false)) (hv (i₀, false))
    convert hm using 1
    ext j
    simp only [vadd_eq_add, vsub_eq_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, vertex_apply, sign, Bool.false_eq_true, if_false, if_true, Pi.zero_apply]
    split_ifs <;> norm_num
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, hz⟩).mp
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin d)).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  have hi := AffineSubspace.vsub_mem_direction (hv (i, true)) hz
  simpa [vertex, sign] using hi

lemma hull_isDPolytope (d : ℕ) (hd : 0 < d) : Grunbaum2003.IsDPolytope (hull d) := by
  refine ⟨⟨Set.range vertex, Set.finite_range vertex, ?_, rfl⟩, hull_affineSpan d hd⟩
  exact ⟨vertex (⟨0, hd⟩, true), Set.mem_range_self _⟩

lemma proper_face_compatible {d : ℕ} {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (hull d) F) (hne : F.Nonempty) (hproper : F ≠ hull d) :
    compatible (Finset.univ.filter (fun p : Fin d × Bool => vertex p ∈ F)) := by
  intro i hboth
  have ht : vertex (i, true) ∈ F := (Finset.mem_filter.mp hboth.1).2
  have hf : vertex (i, false) ∈ F := (Finset.mem_filter.mp hboth.2).2
  obtain ⟨l, hl⟩ := hF hne
  have hvt := ht
  have hvf := hf
  rw [hl] at hvt hvf
  have hneg : l (vertex (i, false)) = -l (vertex (i, true)) := by
    rw [show vertex (i, false) = -vertex (i, true) from vertex_neg (i, true), map_neg]
  have hzero : l (vertex (i, true)) = 0 := by
    have h₁ := hvt.2 (vertex (i, false)) (vertex_mem _)
    have h₂ := hvf.2 (vertex (i, true)) (vertex_mem _)
    rw [hneg] at h₁ h₂
    linarith
  have hbound : ∀ x ∈ hull d, l x ≤ 0 := by
    intro x hx
    simpa [hzero] using hvt.2 x hx
  have hgen : ∀ p : Fin d × Bool, vertex p ∈ F := by
    intro p
    have hp_le := hbound (vertex p) (vertex_mem p)
    have hp_neg := hbound (vertex (p.1, !p.2)) (vertex_mem _)
    rw [vertex_neg, map_neg] at hp_neg
    have hp_zero : l (vertex p) = 0 := by linarith
    rw [hl]
    exact ⟨vertex_mem p, fun x hx => by simpa [hp_zero] using hbound x hx⟩
  apply hproper
  apply Set.Subset.antisymm hF.subset
  apply convexHull_min _ (hF.convex (convex_convexHull ℝ _))
  rintro x ⟨p, rfl⟩
  exact hgen p

lemma face_eq_label_hull {d : ℕ} {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (hull d) F) :
    F = convexHull ℝ (vertex '' ((Finset.univ.filter (fun p : Fin d × Bool => vertex p ∈ F) :
      Finset (Fin d × Bool)) : Set (Fin d × Bool))) := by
  have hInc : F ∩ Set.range vertex =
      vertex '' ((Finset.univ.filter (fun p : Fin d × Bool => vertex p ∈ F) :
        Finset (Fin d × Bool)) : Set (Fin d × Bool)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, p, rfl⟩
      exact ⟨p, hx, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, p, rfl⟩
  rw [← hInc]
  exact finite_face_hull vertex hF

lemma compatible_hull_finrank {d : ℕ} {I : Finset (Fin d × Bool)}
    (hI : compatible I) (hne : I.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ
      (vertex '' (I : Set (Fin d × Bool))))).direction + 1 = I.card := by
  have : Nonempty ↥I := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hi := compatible_affineIndependent hI
  have hrange : Set.range (fun p : I => vertex p.val) = vertex '' (I : Set (Fin d × Bool)) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [affineSpan_convexHull, direction_affineSpan, ← hrange]
  simpa only [Fintype.card_coe] using hi.finrank_vectorSpan_add_one

lemma hull_isSimplicial (d : ℕ) (hd : 0 < d) : Grunbaum2003.IsSimplicialDPolytope (hull d) := by
  refine ⟨hull_isDPolytope d hd, ?_⟩
  intro F hne hF hdim
  have hproper : F ≠ hull d := by
    intro h
    rw [h, hull_affineSpan d hd, AffineSubspace.direction_top,
      finrank_top, Module.finrank_fin_fun] at hdim
    omega
  let I : Finset (Fin d × Bool) := Finset.univ.filter (fun p => vertex p ∈ F)
  have hI : compatible I := proper_face_compatible hF hne hproper
  have hFEq : F = convexHull ℝ (vertex '' (I : Set (Fin d × Bool))) := face_eq_label_hull hF
  have hIne : I.Nonempty := by
    have hh : (convexHull ℝ (vertex '' (I : Set (Fin d × Bool)))).Nonempty := hFEq ▸ hne
    obtain ⟨_, p, hp, rfl⟩ := convexHull_nonempty_iff.mp hh
    exact ⟨p, Finset.mem_coe.mp hp⟩
  have hrank := compatible_hull_finrank hI hIne
  rw [← hFEq] at hrank
  have hcard : d = I.card := hdim.symm.trans hrank
  let e : Fin d ≃ ↥I := Fintype.equivOfCardEq (by simpa using hcard)
  have hind := compatible_affineIndependent hI
  refine ⟨(fun p : I => vertex p.val) ∘ e, hind.comp_embedding e.toEmbedding, ?_⟩
  rw [e.surjective.range_comp (fun p : I => vertex p.val), hFEq]
  congr 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.property, rfl⟩

lemma hull_faceCount {d : ℕ} (hd : 0 < d) (k : ℕ) (hk : k < d) :
    Grunbaum2003.faceCount (hull d) k =
      (((Finset.univ : Finset (Fin d × Bool)).powersetCard (k + 1)).filter compatible).card := by
  let S : Set (Set (Fin d → ℝ)) :=
    {F | F.Nonempty ∧ IsExposed ℝ (hull d) F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = k}
  let T : Finset (Finset (Fin d × Bool)) :=
    ((Finset.univ : Finset (Fin d × Bool)).powersetCard (k + 1)).filter compatible
  let f : Finset (Fin d × Bool) → Set (Fin d → ℝ) :=
    fun I => convexHull ℝ (vertex '' (I : Set (Fin d × Bool)))
  have hfInj : Set.InjOn f (T : Set (Finset (Fin d × Bool))) := by
    intro I hI J hJ heq
    have hIc := (Finset.mem_filter.mp hI).2
    have hJc := (Finset.mem_filter.mp hJ).2
    have hIcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hI).1).2
    have hJcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hJ).1).2
    have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    ext p
    rw [← (compatible_face hIc hIne).2 p, ← (compatible_face hJc hJne).2 p]
    change vertex p ∈ f I ↔ vertex p ∈ f J
    rw [heq]
  have hfImage : f '' (T : Set (Finset (Fin d × Bool))) = S := by
    ext F
    constructor
    · rintro ⟨I, hI, rfl⟩
      have hIc := (Finset.mem_filter.mp hI).2
      have hIcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hI).1).2
      have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨?_, (compatible_face hIc hIne).1, ?_⟩
      · exact ((Finset.coe_nonempty.mpr hIne).image vertex).convexHull
      · have hrank := compatible_hull_finrank hIc hIne
        change Module.finrank ℝ (affineSpan ℝ (f I)).direction + 1 = I.card at hrank
        omega
    · rintro ⟨hFne, hFexp, hrank⟩
      have hproper : F ≠ hull d := by
        intro h
        rw [h, hull_affineSpan d hd, AffineSubspace.direction_top,
          finrank_top, Module.finrank_fin_fun] at hrank
        omega
      let I : Finset (Fin d × Bool) := Finset.univ.filter (fun p => vertex p ∈ F)
      have hIc : compatible I := proper_face_compatible hFexp hFne hproper
      have hFEq : F = f I := face_eq_label_hull hFexp
      have hIne : I.Nonempty := by
        have hh : (f I).Nonempty := hFEq ▸ hFne
        obtain ⟨_, p, hp, rfl⟩ := convexHull_nonempty_iff.mp hh
        exact ⟨p, Finset.mem_coe.mp hp⟩
      have hdim := compatible_hull_finrank hIc hIne
      change Module.finrank ℝ (affineSpan ℝ (f I)).direction + 1 = I.card at hdim
      rw [← hFEq] at hdim
      have hcard : I.card = k + 1 := by omega
      exact ⟨I, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hcard⟩, hIc⟩, hFEq.symm⟩
  change S.ncard = T.card
  rw [← hfImage, hfInj.ncard_image, Set.ncard_coe_finset]

lemma hull_four_faceCounts :
    Grunbaum2003.faceCount (hull 4) 0 = 8 ∧
    Grunbaum2003.faceCount (hull 4) 1 = 24 ∧
    Grunbaum2003.faceCount (hull 4) 2 = 32 ∧
    Grunbaum2003.faceCount (hull 4) 3 = 16 := by
  have h0 := hull_faceCount (d := 4) (by omega) 0 (by omega)
  have h1 := hull_faceCount (d := 4) (by omega) 1 (by omega)
  have h2 := hull_faceCount (d := 4) (by omega) 2 (by omega)
  have h3 := hull_faceCount (d := 4) (by omega) 3 (by omega)
  rw [h0, h1, h2, h3]
  decide +kernel

abbrev crossFourG (i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0

lemma crossFourG_isMSequence : Grunbaum2003.IsMSequence 2 crossFourG := by
  refine ⟨by rfl, ?_⟩
  intro k hk hkle
  interval_cases k
  · refine Or.inr ⟨1, (fun _ => 3), by omega, by omega, by norm_num, ?_, ?_, ?_⟩
    · intro r s hr hrs hs
      omega
    · norm_num [crossFourG]
    · norm_num [crossFourG]
  · refine Or.inr ⟨1, (fun r => r), by omega, by omega, by norm_num, ?_, ?_, ?_⟩
    · intro r s hr hrs hs
      exact hrs
    · decide
    · decide

theorem cross_four_realization :
    ∃ P : Set (Fin 4 → ℝ), Grunbaum2003.IsSimplicialDPolytope P ∧
      Grunbaum2003.faceCount P 0 = 8 ∧
      Grunbaum2003.faceCount P 1 = 24 ∧
      Grunbaum2003.faceCount P 2 = 32 ∧
      Grunbaum2003.faceCount P 3 = 16 ∧
      Grunbaum2003.IsMSequence 2 crossFourG ∧
      ∀ j : Fin 4, (Grunbaum2003.faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range 3, (crossFourG i : ℤ) * Grunbaum2003.gTheoremMatrix 4 i j.succ.val := by
  obtain ⟨h0, h1, h2, h3⟩ := hull_four_faceCounts
  refine ⟨hull 4, hull_isSimplicial 4 (by omega), h0, h1, h2, h3, crossFourG_isMSequence, ?_⟩
  intro j
  fin_cases j <;> norm_num [Finset.sum_range_succ, crossFourG,
    Grunbaum2003.gTheoremMatrix, Nat.choose, h0, h1, h2, h3]

end GHard

theorem solution :
    ∃ P : Set (Fin 4 → ℝ), Grunbaum2003.IsSimplicialDPolytope P ∧
      Grunbaum2003.faceCount P 0 = 8 ∧
      Grunbaum2003.faceCount P 1 = 24 ∧
      Grunbaum2003.faceCount P 2 = 32 ∧
      Grunbaum2003.faceCount P 3 = 16 ∧
      Grunbaum2003.IsMSequence 2 (fun i : ℕ => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0) ∧
      ∀ j : Fin 4, (Grunbaum2003.faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range 3, ((fun i : ℕ => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0) i : ℤ) * Grunbaum2003.gTheoremMatrix 4 i j.succ.val := GHard.cross_four_realization

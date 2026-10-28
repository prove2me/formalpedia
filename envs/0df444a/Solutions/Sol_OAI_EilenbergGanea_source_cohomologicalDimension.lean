-- Prove2me | solution 1 for OAI.EilenbergGanea.source_cohomologicalDimension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T06:55:15.054987+00:00
-- url     : https://prove2.me/submissions/79abe408-2f79-4648-a738-dd44f90fbb00

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEGC004

section
-- module Solutions.OAIEG.RightAngledArtin_Basic
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea


section FiniteGeneration
variable {V : Type*} (L : SimpleGraph V)

theorem edge_difference_mem {v w : V} (h : L.Adj v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L :=
  Subgroup.subset_closure ⟨v, w, h, rfl⟩

theorem reachable_difference_mem {v w : V} (h : L.Reachable v w) :
    artinGenerator L v * (artinGenerator L w)⁻¹ ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    simpa only [mul_assoc, inv_mul_cancel_left] using
      (edgeGenerated L).mul_mem (edge_difference_mem L huv) ih

theorem reachable_inv_difference_mem {v w : V} (h : L.Reachable v w) :
    (artinGenerator L v)⁻¹ * artinGenerator L w ∈ edgeGenerated L := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hc := (adjacent_generators_commute L huv).inv_left
    have he : (artinGenerator L u)⁻¹ * artinGenerator L v ∈ edgeGenerated L := by
      rw [hc.eq]
      exact edge_difference_mem L huv.symm
    simpa only [mul_assoc, mul_inv_cancel_left] using (edgeGenerated L).mul_mem he ih


/-- A group-theoretic conjugation identity used with edge differences. -/
theorem conjugate_mem_of_difference {A : Type*} [Group A] (K : Subgroup A)
    {g a e : A} (hga : g * a⁻¹ ∈ K) (he : e ∈ K) (ha : Commute a e) :
    g * e * g⁻¹ ∈ K := by
  have hm := K.mul_mem (K.mul_mem hga he) (K.inv_mem hga)
  have hi : (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * e * g⁻¹ := by
    calc
      (g * a⁻¹) * e * (g * a⁻¹)⁻¹ = g * (a⁻¹ * e * a) * g⁻¹ := by group
      _ = g * e * g⁻¹ := by rw [ha.inv_left.eq]; simp [mul_assoc]
  rwa [hi] at hm

theorem generator_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    artinGenerator L v * x * (artinGenerator L v)⁻¹ ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤ (edgeGenerated L).comap (MulAut.conj (artinGenerator L v)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    exact conjugate_mem_of_difference (edgeGenerated L)
      (reachable_difference_mem L (hconn v b)) (edge_difference_mem L hbc)
      ((Commute.refl _).mul_right (adjacent_generators_commute L hbc).inv_right)
  exact hh hx

theorem generator_inv_conjugate_mem (hconn : L.Preconnected) (v : V)
    {x : ArtinGroup L} (hx : x ∈ edgeGenerated L) :
    (artinGenerator L v)⁻¹ * x * artinGenerator L v ∈ edgeGenerated L := by
  have hh : edgeGenerated L ≤
      (edgeGenerated L).comap (MulAut.conj ((artinGenerator L v)⁻¹)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨b, c, hbc, rfl⟩
    change (artinGenerator L v)⁻¹ * (artinGenerator L b * (artinGenerator L c)⁻¹) *
      ((artinGenerator L v)⁻¹)⁻¹ ∈ edgeGenerated L
    apply conjugate_mem_of_difference (edgeGenerated L) (a := (artinGenerator L b)⁻¹)
    · simpa using reachable_inv_difference_mem L (hconn v b)
    · exact edge_difference_mem L hbc
    · exact ((Commute.refl _).mul_right
        (adjacent_generators_commute L hbc).inv_right).inv_left
  simpa using hh hx

theorem edgeGenerated_normal (hconn : L.Preconnected) : (edgeGenerated L).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply (Subgroup.eq_top_iff' _).mpr
  apply PresentedGroup.generated_by
  intro v
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact generator_conjugate_mem L hconn v
  · intro hx
    simpa [mul_assoc] using generator_inv_conjugate_mem L hconn v hx

/-- For a connected defining graph, edge differences generate the full height kernel. -/
theorem edgeGenerated_eq_height_kernel (hconn : L.Preconnected) (v₀ : V) :
    edgeGenerated L = (height L).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨v, w, _, rfl⟩
    simp [MonoidHom.mem_ker]
  · let _ := edgeGenerated_normal L hconn
    let q := QuotientGroup.mk' (edgeGenerated L)
    let z := zpowersHom _ (q (artinGenerator L v₀))
    have hq : q = z.comp (height L) := by
      apply PresentedGroup.ext
      intro v
      change q (artinGenerator L v) = z (height L (artinGenerator L v))
      rw [height_generator]
      change q (artinGenerator L v) = q (artinGenerator L v₀) ^ (1 : ℤ)
      rw [zpow_one]
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (reachable_difference_mem L (hconn v v₀))
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq, MonoidHom.comp_apply, (MonoidHom.mem_ker.mp hx), map_one]

end FiniteGeneration

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Seed
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea

theorem seed_vertex_edge_adj {v : SeedVertex} {e : SeedEdge} (h : v ∈ edgeVertices e) :
    seedGraph.Adj (.inl v) (.inr (.inl e)) := Or.inl h

theorem seed_edge_sector_adj {e : SeedEdge} {s : Sector} (h : e ∈ sectorEdges s) :
    seedGraph.Adj (.inr (.inl e)) (.inr (.inr s)) := Or.inl h

theorem rose_vertex_reachable (v : RoseVertex) :
    seedGraph.Reachable seedBase (.inl (.inl v)) := by
  rcases v with _ | ⟨b, i⟩
  · exact .refl _
  · fin_cases i
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 0))))
          (.inr (.inl (.inl (b, 0)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm
    · have h₁ : seedGraph.Adj seedBase (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      have h₂ : seedGraph.Adj (.inl (.inl (some (b, 1))))
          (.inr (.inl (.inl (b, 2)))) := by
        apply seed_vertex_edge_adj
        simp [edgeVertices, circleStart, circleEnd]
      exact h₁.reachable.trans h₂.reachable.symm

theorem seed_vertex_reachable (v : SeedVertex) :
    seedGraph.Reachable seedBase (.inl v) := by
  rcases v with v | r
  · exact rose_vertex_reachable v
  · let s := firstSector r
    have h₁ : seedGraph.Adj (.inl (.inl (sectorStart s))) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices]
    have h₂ : seedGraph.Adj (.inl (.inr r)) (.inr (.inl (.inr s))) := by
      apply seed_vertex_edge_adj
      simp [edgeVertices, s, firstSector]
    exact ((rose_vertex_reachable (sectorStart s)).trans h₁.reachable).trans h₂.reachable.symm

theorem seed_edge_reachable (e : SeedEdge) :
    seedGraph.Reachable seedBase (.inr (.inl e)) := by
  rcases e with e | s
  · apply (seed_vertex_reachable (.inl (circleStart e))).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]
  · apply (seed_vertex_reachable (.inr s.1)).trans
    apply SimpleGraph.Adj.reachable
    apply seed_vertex_edge_adj
    simp [edgeVertices]

theorem seed_cell_reachable (x : SeedCell) : seedGraph.Reachable seedBase x := by
  rcases x with v | e
  · exact seed_vertex_reachable v
  · rcases e with e | s
    · exact seed_edge_reachable e
    · apply (seed_edge_reachable (.inl (sectorCircleEdge s))).trans
      apply SimpleGraph.Adj.reachable
      apply seed_edge_sector_adj
      simp [sectorEdges]

theorem seed_connected : seedGraph.Connected := by
  exact { preconnected := fun v w =>
    (seed_cell_reachable v).symm.trans (seed_cell_reachable w), nonempty := ⟨seedBase⟩ }


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.CliqueCohomology
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
section CliqueSquare
variable {V : Type*} (L : SimpleGraph V)

 theorem heightDifference_commute (v w b : V)
    (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    Commute (heightDifference L v b) (heightDifference L w b) := by
  apply Subtype.ext
  exact (((adjacent_generators_commute L hvw).mul_right
    (adjacent_generators_commute L hvb).inv_right).mul_left
      (((adjacent_generators_commute L hwb).symm.inv_left).mul_right (Commute.refl _)))

end CliqueSquare

section CupCocycle
open groupCohomology
variable {G : Type} [Group G]

/-- Antisymmetrizing on a commuting pair detects a nonzero integral class. -/
theorem exponentCup_not_coboundary (a b : G →* Multiplicative ℤ) (g h : G)
    (hc : Commute g h)
    (hag : (a g).toAdd = 1) (hah : (a h).toAdd = 0)
    (hbg : (b g).toAdd = 0) (hbh : (b h).toAdd = 1) :
    ⇑(exponentCup a b) ∉ coboundaries₂ (Rep.trivial ℤ G ℤ) := by
  rintro ⟨f, hf⟩
  have h₁ := congrFun hf (g, h)
  have h₂ := congrFun hf (h, g)
  change f h - f (g*h) + f g = (a g).toAdd * (b h).toAdd at h₁
  change f g - f (h*g) + f h = (a h).toAdd * (b g).toAdd at h₂
  rw [hag, hbh] at h₁
  rw [hah, hbg, ← hc.eq] at h₂
  change (f h : ℤ) - f (g*h) + f g = 1 * 1 at h₁
  change (f g : ℤ) - f (g*h) + f h = 0 * 0 at h₂
  linarith

theorem exponentCup_class_ne_zero (a b : G →* Multiplicative ℤ) (g h : G)
    (hc : Commute g h)
    (hag : (a g).toAdd = 1) (hah : (a h).toAdd = 0)
    (hbg : (b g).toAdd = 0) (hbh : (b h).toAdd = 1) :
    H2π _ (exponentCup a b) ≠ 0 := by
  intro he
  exact exponentCup_not_coboundary a b g h hc hag hah hbg hbh
    ((H2π_eq_zero_iff (A := Rep.trivial ℤ G ℤ) (exponentCup a b)).mp he)

end CupCocycle

section CliqueCohomology
open groupCohomology
variable {V : Type} (L : SimpleGraph V)

theorem clique_exponent_class_nonzero (v w b : V)
    (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    ∃ x : H2 (Rep.trivial ℤ (height L).ker ℤ), x ≠ 0 := by
  classical
  let a := (generatorExponent L v).comp (height L).ker.subtype
  let d := (generatorExponent L w).comp (height L).ker.subtype
  have hvw' := L.ne_of_adj hvw
  have hvb' := L.ne_of_adj hvb
  have hwb' := L.ne_of_adj hwb
  refine ⟨H2π _ (exponentCup a d), exponentCup_class_ne_zero a d
    (heightDifference L v b) (heightDifference L w b)
    (heightDifference_commute L v w b hvw hvb hwb) ?_ ?_ ?_ ?_⟩
  all_goals simp [a, d, heightDifference, hvw', hvw'.symm, hvb'.symm, hwb'.symm]

end CliqueCohomology


open CategoryTheory CategoryTheory.Limits

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {X Y : C} (P : ProjectiveResolution X) (F : C ⥤ D)
    [F.Additive] [F.Full] [F.Faithful]
    [F.PreservesProjectiveObjects] [F.PreservesHomology]

/-- Vanishing in the literal projective-dimension sense forces every
2-cocycle in a projective resolution to be a coboundary; the fully faithful
exact functor permits us to use this for the representation/group-ring equivalence. -/
theorem cocycle_boundary_of_projectiveDimension_lt_two
    [HasProjectiveDimensionLT (F.obj X) 2]
    (f : P.complex.X 2 ⟶ Y) (hf : P.complex.d 3 2 ≫ f = 0) :
    ∃ g : P.complex.X 1 ⟶ Y, P.complex.d 2 1 ≫ g = f := by
  let := HasExt.standard D
  let Q := F.mapProjectiveResolution P
  have hmf : Q.complex.d 3 2 ≫ F.map f = 0 := by
    change F.map (P.complex.d 3 2) ≫ F.map f = 0
    rw [← F.map_comp, hf, F.map_zero]
  have hc := Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT (Q.extMk (F.map f) 3 rfl hmf) 2 (by rfl)
  obtain ⟨g, hg⟩ := (Q.extMk_eq_zero_iff (F.map f) 3 rfl hmf 1 rfl).mp hc
  change F.obj (P.complex.X 1) ⟶ F.obj Y at g
  change F.map (P.complex.d 2 1) ≫ g = F.map f at hg
  refine ⟨F.preimage g, F.map_injective ?_⟩
  rw [F.map_comp, F.map_preimage]
  exact hg

/-- The same vanishing expressed in the library's older linear-Yoneda model
of Ext. This theorem proves rather than assumes the bridge between the two APIs. -/
theorem isZero_homology_two_of_projectiveDimension_lt_two
    (R : Type*) [Ring R] [Linear R C]
    [HasProjectiveDimensionLT (F.obj X) 2] :
    IsZero ((P.complex.linearYonedaObj R Y).homology 2) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change P.complex.d 3 2 ≫ f = 0 at hf
  exact cocycle_boundary_of_projectiveDimension_lt_two P F f hf
end

open CategoryTheory CategoryTheory.Limits

theorem two_le_cohomologicalDimension_of_H2_nonzero (G : Type) [Group G]
    (hx : ∃ x : groupCohomology.H2 (Rep.trivial ℤ G ℤ), x ≠ 0) :
    2 ≤ cohomologicalDimension G := by
  change (2 : ℕ) ≤ CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ G) (Representation.trivial ℤ G ℤ).asModule)
  rw [CategoryTheory.projectiveDimension_ge_iff]
  intro hd
  let F := Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)
  let P := Rep.barResolution ℤ G
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  have : HasProjectiveDimensionLT (F.obj (Rep.trivial ℤ G ℤ)) 2 := hd
  have hz := isZero_homology_two_of_projectiveDimension_lt_two
    (Y := Rep.trivial ℤ G ℤ) P F ℤ
  have hz' : IsZero (groupCohomology.H2 (Rep.trivial ℤ G ℤ)) :=
    hz.of_iso (groupCohomologyIso (Rep.trivial ℤ G ℤ) 2 P)
  obtain ⟨x, hx⟩ := hx
  exact hx ((ModuleCat.isZero_iff_subsingleton.mp hz').elim x 0)

theorem height_kernel_two_le_cohomologicalDimension {V : Type} (L : SimpleGraph V)
    (v w b : V) (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    2 ≤ cohomologicalDimension (height L).ker :=
  two_le_cohomologicalDimension_of_H2_nonzero _ (clique_exponent_class_nonzero L v w b hvw hvb hwb)

theorem source_two_le_cohomologicalDimension : 2 ≤ cohomologicalDimension SourceGroup := by
  apply height_kernel_two_le_cohomologicalDimension seedGraph seedCliqueVertex seedCliqueEdge seedCliqueFace
  · change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueVertex, seedCliqueEdge, edgeVertices, circleStart]
  · change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueVertex, seedCliqueFace, sectorVertices, sectorEdges, edgeVertices, sectorCircleEdge, sectorLetter, seedWord, circleStart, circleEnd]
  · change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueEdge, seedCliqueFace, sectorEdges, sectorCircleEdge, sectorLetter, seedWord]
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Chains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace CubicalChains
variable {G A : Type*} [Group G]

omit [Group G] in
 theorem cone_absent_upper (a : G → A) (g : G) (w : List A) (ha : a g ∉ w) :
    cone a (upperTerm g w) = -front (a g) (upperTerm g w) := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction (p := fun c _ => cone a c = -front (a g) c) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,hs,_⟩,rfl⟩
    have ha' : a g' ∉ w' := fun hm => ha (hs.subset hm)
    simp [coneTerm,ha']
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,neg_add]
  · intro n c _ hc; simp only [map_smul,hc,smul_neg]

omit [Group G] in
 theorem cone_front_present (a : G → A) (g : G) (w : List A) :
    cone a (front (a g) (upperTerm g w)) = 0 := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction
    (p := fun c _ => cone a (front (a g) c) = 0) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,_,_⟩,rfl⟩
    simp [coneTerm]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

omit [Group G] in
 theorem upper_cone_identity (a : G → A) (g : G) (w : List A)
    (hw : a g ∉ w ∨ ∃ u, w = a g :: u ∧ a g ∉ u) :
    upper (coneTerm a g w) + cone a (upperTerm g w) = Finsupp.single (g,w) 1 := by
  rcases hw with ha | ⟨u,rfl,hu⟩
  · rw [coneTerm,ite_eq_right ha,map_neg,upper_single,one_smul,upperTerm_cons,
      cone_absent_upper a g w ha,neg_sub]
    abel
  · simp only [coneTerm,List.mem_cons_self,↓reduceIte,map_zero,upperTerm_cons,
      map_sub,map_neg,cone_single,one_smul,cone_front_present,coneTerm,ite_eq_right hu]
    abel


omit [Group G] in
 theorem Removed.mem {x : A} {w u : List A} (h : Removed x w u) : x ∈ w := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  simp

omit [Group G] in
 theorem Removed.not_mem {x : A} {w u : List A} (h : Removed x w u) (hw : w.Nodup) : x ∉ u := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  rw [List.mem_append,not_or]
  refine ⟨?_,(List.nodup_cons.mp (List.nodup_append.mp hw).2.1).1⟩
  intro hx
  exact (List.nodup_append.mp hw).2.2 x hx x (by simp) rfl

variable [LinearOrder A]

namespace DescentSystem
variable {v : A → G} (D : DescentSystem v)

theorem valid_sublist {g : G} {w u : List A} (hw : D.Valid g w) (hu : u.Sublist w) : D.Valid g u :=
  ⟨hw.1.sublist hu,fun x hx => hw.2 x (hu.subset hx)⟩

theorem valid_nodup {g : G} {w : List A} (hw : D.Valid g w) : w.Nodup := hw.1.imp_of_mem (by
  intro x y _ _ h; exact ne_of_lt h)

theorem valid_removed {g : G} {w u : List A} {x : A}
    (hw : D.Valid g w) (hu : Removed x w u) : D.Valid (g*v x) u := by
  refine ⟨hw.1.sublist hu.sublist,?_⟩
  intro y hy
  exact D.preserve g x y (hw.2 x hu.mem) (hw.2 y (hu.sublist.subset hy))
    (fun he => hu.not_mem (D.valid_nodup hw) (he ▸ hy))

theorem valid_zero_length {g : G} {w : List A} (hw : D.Valid g w) (hg : D.length g = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons x w => have := D.step g x (hw.2 x (by simp)); omega

theorem choose_head {g : G} {w : List A} (hw : D.Valid g w) :
    D.choose g ∉ w ∨ ∃ u, w = D.choose g :: u ∧ D.choose g ∉ u := by
  by_cases ha : D.choose g ∈ w
  · right
    cases w with
    | nil => simp at ha
    | cons x w =>
        have hp := List.pairwise_cons.mp hw.1
        have hx : D.choose g = x := by
          rcases List.mem_cons.mp ha with h | h
          · exact h
          · exact False.elim ((not_lt_of_ge (D.choose_le g x (hw.2 x (by simp))))
              (hp.1 (D.choose g) h))
        subst x
        exact ⟨w,rfl,(List.nodup_cons.mp (D.valid_nodup hw)).1⟩
  · exact Or.inl ha

theorem valid_cone {g : G} {w : List A} (hw : D.Valid g w)
    (hg : 0 < D.length g) (ha : D.choose g ∉ w) : D.Valid g (D.choose g :: w) := by
  refine ⟨List.pairwise_cons.mpr ⟨?_,hw.1⟩,?_⟩
  · intro y hy
    exact lt_of_le_of_ne (D.choose_le g y (hw.2 y hy)) (fun he => ha (he ▸ hy))
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact D.choose_mem g hg
    · exact hw.2 y hy

theorem upperTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    upperTerm g w ∈ D.admissible (w.length-1) (D.length g) := by
  apply Finsupp.supported_mono _ (upperTerm_supported g w)
  rintro ⟨g',w'⟩ ⟨rfl,hs,hl⟩
  exact ⟨D.valid_sublist hw hs,by omega,le_rfl⟩

theorem lowerTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    lowerTerm v g w ∈ D.admissible (w.length-1) (D.length g-1) := by
  apply Finsupp.supported_mono _ (lowerTerm_supported v g w)
  rintro ⟨g',w'⟩ ⟨x,hs,rfl⟩
  have hl := D.step g x (hw.2 x hs.mem)
  exact ⟨D.valid_removed hw hs,by have := hs.length; omega,by simpa using (show D.length (g*v x) ≤ D.length g-1 by omega)⟩

theorem homotopyTerm_admissible {g : G} {w : List A} (hw : D.Valid g w) :
    D.homotopyTerm g w ∈ D.admissible (w.length+1) (D.length g) := by
  unfold homotopyTerm coneTerm
  split
  · exact Submodule.zero_mem _
  · rename_i hg
    split
    · exact Submodule.zero_mem _
    · rename_i ha
      apply Submodule.neg_mem
      exact Finsupp.single_mem_supported ℤ 1 ⟨D.valid_cone hw (Nat.pos_of_ne_zero hg) ha,rfl,le_rfl⟩


theorem admissible_mono {k N M : ℕ} (hNM : N ≤ M) : D.admissible k N ≤ D.admissible k M := by
  apply Finsupp.supported_mono
  rintro p ⟨hv,hk,hl⟩
  exact ⟨hv,hk,hl.trans hNM⟩

theorem upper_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    upper c ∈ D.admissible (k-1) N := by
  apply supported_map upper _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [upper_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono hN (D.upperTerm_admissible hw)

theorem lower_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    lower v c ∈ D.admissible (k-1) (N-1) := by
  apply supported_map (lower v) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [lower_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono (Nat.sub_le_sub_right hN 1) (D.lowerTerm_admissible hw)

theorem boundary_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    boundary v c ∈ D.admissible (k-1) N := by
  have h : boundary v c = upper c + lower v c := by simp [lower]
  rw [h]
  exact Submodule.add_mem _ (D.upper_admissible hc)
    (D.admissible_mono (Nat.sub_le _ _) (D.lower_admissible hc))

theorem homotopy_admissible {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    D.homotopy c ∈ D.admissible (k+1) N := by
  apply supported_map D.homotopy _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk,hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk hN
  simp only [homotopy_single,one_smul]
  simpa only [admissible,hk] using D.admissible_mono hN (D.homotopyTerm_admissible hw)

theorem boundary_squared {k N : ℕ} {c : Chains G A} (hc : c ∈ D.admissible k N) :
    boundary v (boundary v c) = 0 := by
  rw [admissible,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => boundary v (boundary v c) = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_,_⟩,rfl⟩
    simp only [boundary_single,one_smul]
    apply boundary_boundaryTerm
    exact hw.1.imp_of_mem (fun {x y} hx hy h => D.commute g x y (hw.2 x hx) (hw.2 y hy) (ne_of_lt h))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

theorem homotopy_upperTerm {g : G} (w : List A) (hg : D.length g ≠ 0) :
    D.homotopy (upperTerm g w) = cone D.choose (upperTerm g w) := by
  have hh := upperTerm_supported g w
  rw [Finsupp.supported_eq_span_single] at hh
  apply Submodule.span_induction
    (p := fun c _ => D.homotopy c = cone D.choose c) _ _ _ _ hh
  · rintro _ ⟨⟨g',w'⟩,⟨rfl,_,_⟩,rfl⟩
    simp only [homotopy_single,cone_single,one_smul,homotopyTerm,ite_eq_right hg]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

theorem upper_homotopy_identity {g : G} {w : List A} (hw : D.Valid g w)
    (hg : D.length g ≠ 0) :
    upper (D.homotopyTerm g w) + D.homotopy (upperTerm g w) = Finsupp.single (g,w) 1 := by
  rw [homotopyTerm,ite_eq_right hg,D.homotopy_upperTerm w hg]
  exact upper_cone_identity D.choose g w (D.choose_head hw)

theorem remainder_single {g : G} {w : List A} (hw : D.Valid g w) (hg : D.length g ≠ 0) :
    D.remainder (Finsupp.single (g,w) 1) =
      -(lower v (D.homotopyTerm g w) + D.homotopy (lowerTerm v g w)) := by
  have he := D.upper_homotopy_identity hw hg
  simp only [remainder,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.id_apply,
    homotopy_single,boundary_single,one_smul]
  simp only [lower,LinearMap.sub_apply,lowerTerm,map_sub]
  rw [← he]
  abel

theorem remainder_admissible {k N : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ D.admissible k (N+1)) : D.remainder c ∈ D.admissible k N := by
  apply supported_map D.remainder _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hk',hN⟩
  dsimp only [Prod.fst,Prod.snd] at hw hk' hN
  have hpos : D.length g ≠ 0 := by
    intro hz
    have he := D.valid_zero_length hw hz
    simp only [he,List.length_nil] at hk'
    omega
  rw [D.remainder_single hw hpos]
  apply Submodule.neg_mem
  apply Submodule.add_mem
  · have hh := D.lower_admissible (D.homotopyTerm_admissible hw)
    have hNN : D.length g - 1 ≤ N := by omega
    simpa only [admissible,Nat.add_sub_cancel,hk'] using D.admissible_mono hNN hh
  · have hh := D.homotopy_admissible (D.lowerTerm_admissible hw)
    have hlen : w.length - 1 + 1 = k := by omega
    have hNN : D.length g - 1 ≤ N := by omega
    simpa only [admissible,hlen] using D.admissible_mono hNN hh

theorem admissible_zero {k : ℕ} (hk : 0 < k) : D.admissible k 0 = ⊥ := by
  apply le_antisymm _ bot_le
  suffices he : {p : G × List A | D.Valid p.1 p.2 ∧ p.2.length = k ∧ D.length p.1 ≤ 0} = ∅ by
    change Finsupp.supported ℤ ℤ _ ≤ ⊥
    rw [he,Finsupp.supported_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨g,w⟩ ⟨hw,hl,hg⟩
  dsimp only [Prod.fst,Prod.snd] at hw hl hg
  have he := D.valid_zero_length hw (by omega)
  simp only [he,List.length_nil] at hl
  omega

/-- Finite-support descending-cube contraction: every positive-dimensional
cycle bounds, with no topological exactness or contractibility assumption. -/
theorem cycle_bounds {k N : ℕ} (hk : 0 < k) (c : Chains G A)
    (hc : c ∈ D.admissible k N) (hz : boundary v c = 0) :
    ∃ b ∈ D.admissible (k+1) N, boundary v b = c := by
  induction N generalizing c with
  | zero =>
      rw [D.admissible_zero hk,Submodule.mem_bot] at hc
      subst c
      exact ⟨0,Submodule.zero_mem _,map_zero _⟩
  | succ N ih =>
      let r := D.remainder c
      have hr : r = c - boundary v (D.homotopy c) := by
        simp [r,remainder,hz]
      have hrz : boundary v r = 0 := by
        rw [hr,map_sub,hz,D.boundary_squared (D.homotopy_admissible hc),sub_zero]
      obtain ⟨b,hb,hdb⟩ := ih r (D.remainder_admissible hk hc) hrz
      refine ⟨D.homotopy c + b,Submodule.add_mem _ (D.homotopy_admissible hc)
        (D.admissible_mono (Nat.le_succ N) hb),?_⟩
      rw [map_add,hdb,hr]
      abel

end DescentSystem
end CubicalChains


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_ArtinChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder (Letter V)]

theorem descending_finite_bound {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    ∃ N, c ∈ (artinDescentSystem L).admissible k N := by
  refine ⟨c.support.sup (fun p => artinLength L p.1),?_⟩
  apply (Finsupp.mem_supported ℤ c).mpr
  intro p hp
  have hv := (Finsupp.mem_supported ℤ c).mp hc hp
  refine ⟨hv.1,hv.2,?_⟩
  exact Finset.le_sup (f := fun p => artinLength L p.1) hp

/-- Exactness of the genuine descending cubical chain complex in every
positive degree, with no finite-support bound imposed on the cycle. -/
theorem descending_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) (Letter V)) (hc : c ∈ descendingChains L k)
    (hz : boundary (fun x => letterValue (artinGenerator L) (invLetter x)) c = 0) :
    ∃ b ∈ descendingChains L (k+1),
      boundary (fun x => letterValue (artinGenerator L) (invLetter x)) b = c := by
  obtain ⟨N,hN⟩ := descending_finite_bound L hc
  obtain ⟨b,hb,hdb⟩ := (artinDescentSystem L).cycle_bounds hk c hN hz
  refine ⟨b,?_,hdb⟩
  apply Finsupp.supported_mono _ hb
  rintro p ⟨hv,hl,_⟩
  exact ⟨hv,hl⟩

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V)

theorem origin_descent_invariant (g : ArtinGroup L) (w : Word V) (y : Letter V)
    (hw : ∀ x ∈ w, Independent L x y) :
    y ∈ rightDescents L (origin (artinGenerator L) g w) ↔ y ∈ rightDescents L g := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      have hh : ∀ z ∈ w, Independent L z y := fun z hz => hw z (by simp [hz])
      simp only [origin]
      split
      · rw [ih _ hh]
        exact descent_independent_step L g (x := (x.1,false)) (hw x (by simp))
      · exact ih _ hh

/-- Reorientation is invertible on every actual descending cube. -/
theorem orient_origin (g : ArtinGroup L) (w : Word V)
    (hw : w.Pairwise (Independent L)) (hd : ∀ x ∈ w, x ∈ rightDescents L g) :
    orient L (origin (artinGenerator L) g w) (w.map Prod.fst) = (g,w) := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      obtain ⟨hx,hwtail⟩ := List.pairwise_cons.mp hw
      have hdw : ∀ y ∈ w, y ∈ rightDescents L g := fun y hy => hd y (by simp [hy])
      have hdx := hd x (by simp)
      rcases x with ⟨q,b⟩
      cases b
      · have hp : (q,false) ∈ rightDescents L (origin (artinGenerator L) g w) :=
          (origin_descent_invariant L g w (q,false) (fun y hy => (hx y hy).symm)).mpr hdx
        simp only [origin,Bool.false_eq_true,↓reduceIte,List.map_cons,orient,ite_eq_left hp]
        rw [ih g hwtail hdw]
      · have hp : (q,false) ∉ rightDescents L (origin (artinGenerator L) (g * (artinGenerator L q)⁻¹) w) := by
          rw [origin_descent_invariant L _ w (q,false) (fun y hy => (hx y hy).symm)]
          have hh := reverse_step_descent L g (q,false)
          simpa only [letterValue,invLetter,Bool.not_false,Bool.false_eq_true,ite_false] using (not_congr hh).mpr (not_not.mpr hdx)
        simp only [origin,↓reduceIte,List.map_cons,orient,ite_eq_right hp]
        have he : origin (artinGenerator L) (g * (artinGenerator L q)⁻¹) w * artinGenerator L q =
            origin (artinGenerator L) g w := by
          rw [origin_shift]
          · group
          · intro y hy
            exact (adjacent_generators_commute L (hx y hy)).inv_left
        rw [he,ih g hwtail hdw]

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]

attribute [local instance] OAI.EilenbergGanea.TraceWords.CubeDescents.signedLexOrder
attribute [local instance] OAI.EilenbergGanea.TraceWords.CubeDescents.signedPreorder
theorem descending_independent {g : ArtinGroup L} {w : Word V}
    (hw : (artinDescentSystem L).Valid g w) : w.Pairwise (Independent L) := by
  apply hw.1.imp_of_mem
  intro x y hx hy hlt
  exact rightDescents_pairwise L g (hw.2 x hx) (hw.2 y hy) (ne_of_lt hlt)

omit [Fintype V] [Nonempty V] in
theorem signed_sorted_iff {w : Word V} (hw : w.Pairwise (Independent L)) :
    w.Pairwise (· < ·) ↔ (w.map Prod.fst).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  constructor
  · intro hs
    exact (hs.and hw).imp (fun {x y} h => by
      have hh : toLex x < toLex y := h.1
      rcases Prod.Lex.toLex_lt_toLex.mp hh with hlt | ⟨he,_⟩
      · exact hlt
      · exact False.elim (h.2.ne he))
  · intro hs
    exact hs.imp (fun {_ _} hh => Prod.Lex.toLex_lt_toLex.mpr (Or.inl hh))

theorem normalize_descending {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) : normalize (artinGenerator L) c ∈ positiveChains L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hv,hl⟩
  rw [normalize_single,one_smul,normalTerm]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  have hi := descending_independent L hv
  exact ⟨(signed_sorted_iff L hi).mp hv.1,by rw [List.pairwise_map]; exact hi,
    by simpa using hl⟩

theorem denormalize_positive {k : ℕ} {c : Chains (ArtinGroup L) V}
    (hc : c ∈ positiveChains L k) : denormalize L c ∈ descendingChains L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hs,ha,hl⟩
  rw [denormalize_single,one_smul,denormalTerm]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  have hm := orient_map L g w
  have hi : (orient L g w).2.Pairwise (Independent L) := by
    rw [← hm] at ha
    rw [List.pairwise_map] at ha
    exact ha
  refine ⟨⟨(signed_sorted_iff L hi).mpr (by rw [hm]; exact hs),
    orient_descents L g w ha⟩,?_⟩
  rw [← hm,List.length_map] at hl
  exact hl

omit [Fintype V] [Nonempty V] [LinearOrder V] in
theorem normal_denormal_term (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    normalize (artinGenerator L) (denormalTerm L g w) = Finsupp.single (g,w) 1 := by
  rw [denormalTerm,map_smul]
  rcases he : orient L g w with ⟨g',u⟩
  simp only [normalize_single,normalTerm,smul_smul,one_mul,sign_sq,one_smul]
  have ho := origin_orient L g w hw
  have hm := orient_map L g w
  simp only [he] at ho hm
  rw [ho,hm]

theorem denormal_normal_term {g : ArtinGroup L} {w : Word V}
    (hw : (artinDescentSystem L).Valid g w) :
    denormalize L (normalTerm (artinGenerator L) g w) = Finsupp.single (g,w) 1 := by
  simp only [normalTerm,map_smul,denormalize_single,one_smul,denormalTerm]
  rw [orient_origin L g w (descending_independent L hw) hw.2]
  simp only [smul_smul,sign_sq,one_smul]

omit [Fintype V] [Nonempty V] in
theorem normal_denormal {k : ℕ} {c : Chains (ArtinGroup L) V}
    (hc : c ∈ positiveChains L k) : normalize (artinGenerator L) (denormalize L c) = c := by
  rw [positiveChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    normalize (artinGenerator L) (denormalize L c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,ha,_⟩,rfl⟩
    simpa only [denormalize_single,one_smul] using normal_denormal_term L g w ha
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

theorem denormal_normal {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) : denormalize L (normalize (artinGenerator L) c) = c := by
  rw [descendingChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    denormalize L (normalize (artinGenerator L) c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hv,_⟩,rfl⟩
    simpa only [normalize_single,one_smul] using denormal_normal_term L hv
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

omit [Fintype V] [Nonempty V] [LinearOrder V] in
theorem step_eq_inverse_letter : step (artinGenerator L) =
    fun x => letterValue (artinGenerator L) (invLetter x) := by
  funext x
  cases hx : x.2 <;> simp [step,letterValue,invLetter,hx]

theorem descending_boundary {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    boundary (step (artinGenerator L)) c ∈ descendingChains L (k-1) := by
  obtain ⟨N,hN⟩ := descending_finite_bound L hc
  have hb := (artinDescentSystem L).boundary_admissible hN
  rw [step_eq_inverse_letter]
  apply Finsupp.supported_mono _ hb
  rintro p ⟨hv,hl,_⟩
  exact ⟨hv,hl⟩

theorem normalize_boundary {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    normalize (artinGenerator L) (boundary (step (artinGenerator L)) c) =
      boundary (artinGenerator L) (normalize (artinGenerator L) c) := by
  rw [descendingChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    normalize (artinGenerator L) (boundary (step (artinGenerator L)) c) =
      boundary (artinGenerator L) (normalize (artinGenerator L) c)) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hv,_⟩,rfl⟩
    simp only [boundary_single,normalize_single,one_smul]
    exact normalize_boundaryTerm _ g w ((descending_independent L hv).imp
      (fun {_ _} h => adjacent_generators_commute L h))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

/-- Exactness of the standard positively oriented RAAG cube chains. This is
an actual finite integral filling, derived from the descending contraction. -/
theorem positive_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) V) (hc : c ∈ positiveChains L k)
    (hz : boundary (artinGenerator L) c = 0) :
    ∃ b ∈ positiveChains L (k+1), boundary (artinGenerator L) b = c := by
  have hd := denormalize_positive L hc
  have hdz : boundary (step (artinGenerator L)) (denormalize L c) = 0 := by
    have hn : normalize (artinGenerator L)
        (boundary (step (artinGenerator L)) (denormalize L c)) = 0 := by
      rw [normalize_boundary L hd,normal_denormal L hc,hz]
    have he := denormal_normal L (descending_boundary L hd)
    rw [hn,map_zero] at he
    exact he.symm
  obtain ⟨b,hb,hdb⟩ := descending_cycle_bounds L hk (denormalize L c) hd (by rwa [← step_eq_inverse_letter])
  refine ⟨normalize (artinGenerator L) b,normalize_descending L hb,?_⟩
  rw [← normalize_boundary L hb,step_eq_inverse_letter,hdb,normal_denormal L hc]

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
end

section
-- module Solutions.OAIEG.IntegralModules
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

/-! Group-ring augmentation and literal two-syzygy dimension criterion. -/
namespace EilenbergGanea
open CategoryTheory

section ProjectiveBound
variable {R P Q M : Type} [Ring R]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup M] [Module R M]

/-- Two successive projective syzygies give the literal integral upper bound. -/
theorem projectiveDimension_le_two_of_syzygies
    (ε : P →ₗ[R] M) (hε : Function.Surjective ε)
    (d : Q →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    [Module.Projective R P] [Module.Projective R Q]
    [Module.Projective R (LinearMap.ker d)] :
    CategoryTheory.projectiveDimension (ModuleCat.of R M) ≤ 2 := by
  have h₁ := (LinearMap.shortExact_shortComplexKer hd).hasProjectiveDimensionLT_X₃ 1
    (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker d)) 1)
    (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R Q) 2)
  have h₂ := (LinearMap.shortExact_shortComplexKer hε).hasProjectiveDimensionLT_X₃ 2
    h₁ (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R P) 3)
  exact (CategoryTheory.projectiveDimension_le_iff _ 2).mpr h₂
end ProjectiveBound

section CayleyModules
variable {Γ S : Type} [Group Γ]

theorem cayleyAugmentation_surjective :
    Function.Surjective (cayleyAugmentation (Γ := Γ)) := by
  intro n
  refine ⟨MonoidAlgebra.single (1 : Γ) ((Representation.trivial ℤ Γ ℤ).asModuleEquiv n),?_⟩
  rw [cayleyAugmentation_single,LinearEquiv.symm_apply_apply]

 theorem cayleyGeneratorDifference_mem (v : S → Γ) (w : FreeGroup S) :
    MonoidAlgebra.single (FreeGroup.lift v w) 1 - 1 ∈ LinearMap.range (cayleyDifferential v) := by
  induction w using OAI.freeGroupInductionOn with
  | one =>
      simp only [map_one]
      have he : (MonoidAlgebra.single (1 : Γ) 1 : IntegralGroupRing Γ) = 1 := rfl
      rw [he,sub_self]
      exact Submodule.zero_mem _
  | of s =>
      exact ⟨Finsupp.single s 1,by simp⟩
  | inv_of s =>
      refine ⟨Finsupp.single s (-MonoidAlgebra.single (v s)⁻¹ 1),?_⟩
      simp [mul_sub,MonoidAlgebra.single_mul_single]
      rfl
  | mul w z hw hz =>
      have hh := (LinearMap.range (cayleyDifferential v)).smul_mem
        (MonoidAlgebra.single (FreeGroup.lift v w) 1) hz
      have hc := (LinearMap.range (cayleyDifferential v)).add_mem hw hh
      rw [map_mul]
      convert hc using 1
      change _ = (_ - 1) + _ * (_ - 1)
      rw [mul_sub,mul_one,MonoidAlgebra.single_mul_single,one_mul]
      abel

theorem cayleyAugmentation_normalize (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v)) (r : IntegralGroupRing Γ) :
    r - MonoidAlgebra.single 1
      ((Representation.trivial ℤ Γ ℤ).asModuleEquiv (cayleyAugmentation r)) ∈
        LinearMap.range (cayleyDifferential v) := by
  classical
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r t hr ht =>
      rw [map_add, map_add, MonoidAlgebra.single_add]
      convert (LinearMap.range (cayleyDifferential v)).add_mem hr ht using 1; abel
  | single g n =>
      rw [cayleyAugmentation_single, LinearEquiv.apply_symm_apply]
      obtain ⟨w, hw⟩ := hv g
      have hm := (LinearMap.range (cayleyDifferential v)).toAddSubgroup.zsmul_mem
        (cayleyGeneratorDifference_mem v w) n
      rw [hw] at hm
      convert hm using 1
      simp only [smul_sub, MonoidAlgebra.smul_single, zsmul_eq_mul, mul_one]
      rfl

theorem cayley_exact (v : S → Γ) (hv : Function.Surjective (FreeGroup.lift v)) :
    LinearMap.range (cayleyDifferential v) = LinearMap.ker (cayleyAugmentation (Γ := Γ)) := by
  apply le_antisymm
  · rintro _ ⟨r,rfl⟩
    exact LinearMap.congr_fun (cayleyDifferential_aug v) r
  · intro r hr
    have hm := cayleyAugmentation_normalize v hv r
    rw [LinearMap.mem_ker.mp hr, map_zero, MonoidAlgebra.single_zero, sub_zero] at hm
    exact hm

theorem cayleySyzygyDifferential_surjective (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v)) :
    Function.Surjective (cayleySyzygyDifferential v) := by
  intro r
  have hr : (r : IntegralGroupRing Γ) ∈ LinearMap.range (cayleyDifferential v) := by
    rw [cayley_exact v hv]
    exact r.property
  obtain ⟨s, hs⟩ := hr
  exact ⟨s, Subtype.ext hs⟩

theorem cayley_projectiveDimension_le_two (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v))
    [Module.Projective (IntegralGroupRing Γ) (LinearMap.ker (cayleyDifferential v))] :
    CategoryTheory.projectiveDimension
      (ModuleCat.of (IntegralGroupRing Γ) (IntegralTrivialModule Γ)) ≤ 2 := by
  have hk : LinearMap.ker (cayleySyzygyDifferential v) =
      LinearMap.ker (cayleyDifferential v) := LinearMap.ker_codRestrict _ _ _
  have : Module.Projective (IntegralGroupRing Γ)
      (LinearMap.ker (cayleySyzygyDifferential v)) := hk ▸ inferInstance
  exact projectiveDimension_le_two_of_syzygies cayleyAugmentation
    cayleyAugmentation_surjective (cayleySyzygyDifferential v)
    (cayleySyzygyDifferential_surjective v hv)

end CayleyModules
end EilenbergGanea

namespace EilenbergGanea
section ChainPackaging
variable {Γ S T : Type} [Group Γ]

theorem chainPackaging_boundary (v : S → Γ) (c : BasedChains Γ S) :
    cayleyDifferential v (chainPackaging c) = MonoidAlgebra.ofCoeff (edgeBoundary v c) := by
  have he : ((cayleyDifferential v).restrictScalars ℤ).comp
      (chainPackaging (Γ := Γ) (S := S)).toLinearMap =
      (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (edgeBoundary v) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,s⟩ n
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      chainPackaging_single, cayleyDifferential_single, edgeBoundary_single, map_smul,
      map_sub]
    simp only [mul_sub, MonoidAlgebra.single_mul_single, mul_one,
      MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.ofCoeff_single,
      MonoidAlgebra.smul_single, smul_sub, smul_eq_mul]
  exact LinearMap.congr_fun he c

theorem chainPackaging_mem_cycles (v : S → Γ) (c : BasedChains Γ S) :
    c ∈ cycles v ↔ chainPackaging c ∈ LinearMap.ker (cayleyDifferential v) := by
  change edgeBoundary v c = 0 ↔ cayleyDifferential v (chainPackaging c) = 0
  rw [chainPackaging_boundary]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    have hh := congrArg MonoidAlgebra.coeff h
    exact hh

theorem projective_cayley_cycles_of_boundary_basis (v : S → Γ)
    (A : BasedChains Γ T →ₗ[ℤ] BasedChains Γ S) (hA : ChainsEquivariant A)
    (hAi : Function.Injective A) (hAr : LinearMap.range A = cycles v) :
    Module.Projective (IntegralGroupRing Γ) (LinearMap.ker (cayleyDifferential v)) := by
  have hm : ∀ c, chainRingMap A hA c ∈ LinearMap.ker (cayleyDifferential v) := by
    intro c
    apply (chainPackaging_mem_cycles v _).mp
    rw [← hAr]
    exact ⟨chainPackaging.symm c,rfl⟩
  let d := (chainRingMap A hA).codRestrict _ hm
  have hi : Function.Injective d := by
    intro c c' h
    apply (chainPackaging (Γ := Γ) (S := T)).symm.injective
    apply hAi
    apply chainPackaging.injective
    exact congrArg Subtype.val h
  have hs : Function.Surjective d := by
    intro c
    have hc : chainPackaging.symm (c : S →₀ IntegralGroupRing Γ) ∈ cycles v := by
      apply (chainPackaging_mem_cycles v _).mpr
      rw [LinearEquiv.apply_symm_apply]
      exact c.property
    rw [← hAr] at hc
    obtain ⟨b,hb⟩ := hc
    refine ⟨chainPackaging b,Subtype.ext ?_⟩
    change chainPackaging (A (chainPackaging.symm (chainPackaging b))) = c.val
    rw [LinearEquiv.symm_apply_apply,hb,LinearEquiv.apply_symm_apply]
  exact Module.Projective.of_equiv' (LinearEquiv.ofBijective d ⟨hi,hs⟩)

theorem projectiveDimension_le_two_of_boundary_basis (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v))
    (A : BasedChains Γ T →ₗ[ℤ] BasedChains Γ S) (hA : ChainsEquivariant A)
    (hAi : Function.Injective A) (hAr : LinearMap.range A = cycles v) :
    CategoryTheory.projectiveDimension
      (ModuleCat.of (IntegralGroupRing Γ) (IntegralTrivialModule Γ)) ≤ 2 := by
  have := projective_cayley_cycles_of_boundary_basis v A hA hAi hAr
  exact cayley_projectiveDimension_le_two v hv

end ChainPackaging


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.LevelBasis
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))

variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

variable (K : SimplicialChains.Contraction L)
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)
omit [LinearOrder A] in
theorem leftTranslate_front (g : G) (a : A) (c : CubicalChains.Chains G A) :
    leftTranslate g (CubicalChains.front a c) = CubicalChains.front a (leftTranslate g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨q,w⟩; simp
omit [LinearOrder A] in
theorem leftTranslate_boundaryTerm (g q : G) (w : List A) :
    leftTranslate g (boundaryTerm v q w) = boundaryTerm v (g*q) w := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [boundaryTerm_cons,map_sub,leftTranslate_single,leftTranslate_front,ih,mul_assoc]
omit [LinearOrder A] in
theorem leftTranslate_boundary (g : G) (c : CubicalChains.Chains G A) :
    leftTranslate g (boundary v c) = boundary v (leftTranslate g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨q,w⟩; simp [leftTranslate_boundaryTerm]
omit [LinearOrder A] in
theorem leftTranslate_crossPart (g : φ.ker) (c : CubicalChains.Chains G A) :
    leftTranslate g.val (crossPart (ht φ) c) = crossPart (ht φ) (leftTranslate g.val c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n =>
      rcases p with ⟨q,w⟩
      simp only [crossPart,select_single,leftTranslate_single,ht_mul,ht_ker,zero_add]
      split <;> simp_all

theorem includeBasis_translate (k : ℕ) (g : φ.ker) (c : φ.ker × Shape L k →₀ ℤ) :
    includeBasis L φ v root k (translateChains g c) = leftTranslate g.val (includeBasis L φ v root k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n =>
      rcases p with ⟨q,s⟩
      simp only [translateChains_single,includeBasis_single,leftTranslate_single,basisIndex,
        Subgroup.coe_mul,mul_assoc]

include hv in
theorem triangleBoundary_equivariant : ChainsEquivariant (triangleBoundary L φ v root hv) := by
  intro g c
  apply includeBasis_injective L φ v root hv 2
  rw [triangleBoundary_inclusion L φ v root hv,includeBasis_translate,
    ← leftTranslate_boundary,← leftTranslate_crossPart,includeBasis_translate,
    triangleBoundary_inclusion L φ v root hv]

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
variable {V : Type} [LinearOrder V] (L : SimpleGraph V)

/-- The actual oriented crossing-square edges generate precisely the height kernel. -/
theorem generator_surjective (hconn : L.Preconnected) (root : V) :
    Function.Surjective (FreeGroup.lift (generator L (height L) (artinGenerator L) root (height_generator L))) := by
  let f := FreeGroup.lift (generator L (height L) (artinGenerator L) root (height_generator L))
  let F := (height L).ker.subtype.comp f
  have hgen : edgeGenerated L ≤ F.range := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a,b,hadj,rfl⟩
    have hab : a ≠ b := L.ne_of_adj hadj
    rcases lt_or_gt_of_ne hab with hab | hab
    · refine ⟨(FreeGroup.of (pairShape L a b hab hadj))⁻¹,?_⟩
      change (f ((FreeGroup.of (pairShape L a b hab hadj))⁻¹)).val = _
      simp only [f,map_inv,FreeGroup.lift_apply_of,Subgroup.coe_inv,generator_pair,mul_inv_rev,inv_inv]
      exact (adjacent_generators_commute L hadj).inv_right.eq.symm
    · refine ⟨FreeGroup.of (pairShape L b a hab hadj.symm),?_⟩
      change (f (FreeGroup.of (pairShape L b a hab hadj.symm))).val = _
      simp only [f,FreeGroup.lift_apply_of,generator_pair]
      exact (adjacent_generators_commute L hadj).inv_right.eq.symm
  intro g
  have he : g.val ∈ edgeGenerated L := by rw [edgeGenerated_eq_height_kernel L hconn root]; exact g.property
  obtain ⟨w,hw⟩ := hgen he
  exact ⟨w,Subtype.ext hw⟩

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V] (L : SimpleGraph V)

/-- The exactness input to the level slicing is the actual RAAG cube-chain
contraction, not an assumption about a classifying space. -/
theorem artin_total_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) V) (hc : c ∈ total (G := ArtinGroup L) L k)
    (hz : boundary (artinGenerator L) c = 0) :
    ∃ b ∈ total (G := ArtinGroup L) L (k+1), boundary (artinGenerator L) b = c := by
  have he : ∀ n, total (G := ArtinGroup L) L n = TraceWords.CubeDescents.positiveChains L n := by
    intro n
    simp only [total,TraceWords.CubeDescents.positiveChains,SimplicialChains.Valid,and_assoc]
  rw [he] at hc ⊢
  exact TraceWords.CubeDescents.positive_cycle_bounds L hk c hc hz

/-- Integral cd at most two for the genuine height kernel, from a genuine
finite augmented link contraction and the dimension of its flag complex. -/
theorem artin_height_kernel_cd_le_two (root : V) (hconn : L.Preconnected)
    (K : SimplicialChains.Contraction L)
    (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3) :
    cohomologicalDimension (height L).ker ≤ 2 := by
  exact projectiveDimension_le_two_of_boundary_basis
    (generator L (height L) (artinGenerator L) root (height_generator L))
    (generator_surjective L hconn root)
    (triangleBoundary L (height L) (artinGenerator L) root (height_generator L))
    (triangleBoundary_equivariant L (height L) (artinGenerator L) root (height_generator L))
    (triangleBoundary_injective L (height L) (artinGenerator L) root (height_generator L)
      (fun _ _ h => adjacent_generators_commute L h) K (artin_total_cycle_bounds L) dim)
    (triangleBoundary_range L (height L) (artinGenerator L) root (height_generator L)
      (fun _ _ h => adjacent_generators_commute L h) K (artin_total_cycle_bounds L))
end EilenbergGanea.LevelBasis


end

end OAI
end

section
-- module Solutions.OAIEG.Dimension
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

attribute [local instance] OAI.EilenbergGanea.instLinearOrderSeedCell_1
theorem source_valid_length_le (w : List SeedCell) (hw : SimplicialChains.Valid seedGraph w) :
    w.length ≤ 3 := by
  simpa only [List.length_map] using
    SeedChainCertificate.valid_length_le (w.map SeedEncoding.cellEquiv) (source_valid_to_index w hw)

theorem source_cd_eq_two_of_contraction
    (K : SimplicialChains.Contraction SeedChainCertificate.graph) :
    cohomologicalDimension SourceGroup = 2 := by
  apply le_antisymm
  · exact LevelBasis.artin_height_kernel_cd_le_two seedGraph seedBase seed_connected.preconnected
      (sourceLinkContraction K) source_valid_length_le
  · exact source_two_le_cohomologicalDimension

end EilenbergGanea



namespace EilenbergGanea

/-- Literal integral cohomological dimension of the source's fixed group. -/
theorem source_cohomologicalDimension_oai : cohomologicalDimension SourceGroup = 2 :=
  source_cd_eq_two_of_contraction SeedChainCertificate.contraction

end EilenbergGanea



end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.source_cohomologicalDimension_oai := @OAI.EilenbergGanea.source_cohomologicalDimension_oai

-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:38:00.946583+00:00
-- url     : https://prove2.me/submissions/cb06e1d2-652f-44e5-90d9-b39ec5be3ec9

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting
import Theorems.Thm_MICPRep_Periodic_lemma_6_3
import Theorems.Thm_MICPRep_Periodic_lemma_6_6
import Theorems.Thm_MICPRep_Periodic_lemma_6_7
import Theorems.Thm_MICPRep_Periodic_lemma_6_5


open scoped ENNReal Matrix

namespace MICPRep.Periodic.DecompositionChange

noncomputable def affineMap {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) :
    (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ) :=
  (Matrix.toLin' (A.map (fun q : ℚ => (q : ℝ)))).toAffineMap +
    AffineMap.const ℝ (Fin d → ℝ) (fun i => (b i : ℝ))

lemma affineMap_apply {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ)
    (z : Fin d → ℝ) : affineMap A b z = ratAff A b z := rfl

lemma ratAff_comp {d e k : ℕ} (C : Matrix (Fin k) (Fin e) ℚ) (c : Fin k → ℚ)
    (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) (z : Fin d → ℝ) :
    ratAff C c (ratAff A b z) = ratAff (C * A) (C *ᵥ b + c) z := by
  unfold ratAff
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  have hmul : (C * A).map (fun q : ℚ => (q : ℝ)) =
      C.map (fun q : ℚ => (q : ℝ)) * A.map (fun q : ℚ => (q : ℝ)) :=
    Matrix.map_mul (f := Rat.castHom ℝ)
  rw [hmul]
  ext i
  simp only [Pi.add_apply, Rat.cast_add]
  have hvec : (C.map (fun q : ℚ => (q : ℝ)) *ᵥ (fun i => (b i : ℝ))) i =
      ((C *ᵥ b) i : ℝ) := (RingHom.map_mulVec (Rat.castHom ℝ) C b i).symm
  rw [hvec, add_assoc]

lemma ratAff_one_zero {d : ℕ} (z : Fin d → ℝ) :
    ratAff (1 : Matrix (Fin d) (Fin d) ℚ) 0 z = z := by
  simp [ratAff, Matrix.map_one, Pi.zero_def]

lemma inverse_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A) (z : Fin d → ℝ) : ratAffInv A b (ratAff A b z) = z := by
  unfold ratAffInv
  rw [ratAff_comp, A.nonsing_inv_mul (A.isUnit_iff_isUnit_det.mp hA)]
  simp only [add_neg_cancel, ratAff_one_zero]

lemma inverse_right {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A) (z : Fin d → ℝ) : ratAff A b (ratAffInv A b z) = z := by
  unfold ratAffInv
  rw [ratAff_comp, A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA)]
  have hb : A *ᵥ (-(A⁻¹ *ᵥ b)) + b = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA), Matrix.one_mulVec]
    exact neg_add_cancel b
  rw [hb, ratAff_one_zero]

lemma rational_image {d e : ℕ} (I : Set (Fin d → ℝ)) (hI : IsRationallyUnbounded I)
    (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) :
    IsRationallyUnbounded (ratAff A b '' I) := by
  intro k C c
  have hcomp : (fun x ↦ ratAff C c (ratAff A b x)) = ratAff (C * A) (C *ᵥ b + c) :=
    funext (ratAff_comp C c A b)
  rw [Set.image_image, hcomp]
  exact hI k (C * A) (C *ᵥ b + c)

end MICPRep.Periodic.DecompositionChange


namespace MICPRep.Periodic.DecompositionChange

lemma transform {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A)
    (hpre : ∀ z ∈ ratAff A b '' indexSet M ∩ intLattice d, ratAffInv A b z ∈ intLattice d) :
    let M' : Set (Ambient n p d) := {q | (q.1, q.2.1, ratAffInv A b q.2.2) ∈ M}
    let S' : Set (Pt n) :=
      ⋃ z' ∈ ratAff A b '' indexSet M ∩ intLattice d, zProj M (ratAffInv A b z')
    IsRationalFormulation M' S' ∧ indexSet M' = ratAff A b '' indexSet M ∧
      micpDiam M' ≤ micpDiam M := by
  classical
  let R := ratAff A b
  let G := ratAffInv A b
  let M' : Set (Ambient n p d) := {q | (q.1, q.2.1, G q.2.2) ∈ M}
  let S' : Set (Pt n) := ⋃ z' ∈ R '' indexSet M ∩ intLattice d, zProj M (G z')
  change IsRationalFormulation M' S' ∧ indexSet M' = R '' indexSet M ∧
    micpDiam M' ≤ micpDiam M
  have hGR (z : Fin d → ℝ) : G (R z) = z := DecompositionChange.inverse_left A b hA z
  have hRG (z : Fin d → ℝ) : R (G z) = z := DecompositionChange.inverse_right A b hA z
  let L : Ambient n p d →ᵃ[ℝ] Ambient n p d :=
    (AffineMap.id ℝ (Pt n)).prodMap ((AffineMap.id ℝ (Fin p → ℝ)).prodMap
      (DecompositionChange.affineMap A⁻¹ (-(A⁻¹ *ᵥ b))))
  have hclosed : IsClosed M' := hM.1.1.preimage L.continuous_of_finiteDimensional
  have hconvex : Convex ℝ M' := hM.1.2.1.affine_preimage L
  have hindex_inv (z : Fin d → ℝ) : z ∈ indexSet M' ↔ G z ∈ indexSet M := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q.1, q.2.1, G q.2.2), hq, rfl⟩
    · rintro ⟨q, hq, hqz⟩
      refine ⟨(q.1, q.2.1, z), ?_, rfl⟩
      change (q.1, q.2.1, G z) ∈ M
      rw [← hqz]
      exact hq
  have hindex : indexSet M' = R '' indexSet M := by
    ext z
    rw [hindex_inv]
    constructor
    · intro hz
      exact ⟨G z, hz, hRG z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa only [hGR] using hw
  have hGlat (z : Fin d → ℝ) (hz : z ∈ indexSet M' ∩ intLattice d) : G z ∈ intLattice d := by
    apply hpre z
    simpa only [hindex] using hz
  have hfiber (z : Fin d → ℝ) : zProj M' z = zProj M (G z) := rfl
  have hinduce : Induces M' S' := by
    refine ⟨hclosed, hconvex, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨y, hy⟩ := hy
      exact ⟨y, z, hz.2, hy⟩
    · rintro ⟨y, z, hz, hm⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨z, ⟨?_, hz⟩, ⟨y, hm⟩⟩
      rw [← hindex]
      exact ⟨(x, y, z), hm, rfl⟩
  have hdiam : micpDiam M' ≤ micpDiam M := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    rw [hfiber]
    exact le_iSup_of_le (G z) (le_iSup_of_le
      ⟨(hindex_inv z).mp hz.1, hGlat z hz⟩ le_rfl)
  refine ⟨⟨hinduce, ?_⟩, hindex, hdiam⟩
  rw [hindex]
  exact DecompositionChange.rational_image (indexSet M) hM.2 A b

end MICPRep.Periodic.DecompositionChange


namespace MICPRep.Periodic.DecompositionProof

open scoped ENNReal Matrix
set_option maxHeartbeats 800000

lemma convex_index {n p d : ℕ} {M : Set (Ambient n p d)} (hM : Convex ℝ M) :
    Convex ℝ (indexSet M) := by
  let f : Ambient n p d →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun q => q.2.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact hM.linear_image f

lemma lattice_index_nonempty {n p d : ℕ} {M : Set (Ambient n p d)} {S : Set (Pt n)}
    (hM : Induces M S) (hS : S.Nonempty) : (indexSet M ∩ intLattice d).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y, z, hz, hm⟩ := (hM.2.2 x).mp hx
  exact ⟨z, ⟨(x,y,z), hm, rfl⟩, hz⟩

lemma affine_integer_nonempty {d : ℕ} {I : Set (Fin d → ℝ)}
    (hZ : (I ∩ intLattice d).Nonempty) : (affZ I : Set (Fin d → ℝ)).Nonempty := by
  obtain ⟨z, hz⟩ := hZ
  exact ⟨z, mem_affineSpan ℝ hz⟩

lemma rank_zero_good {d : ℕ} {I : Set (Fin d → ℝ)}
    (hZ : (I ∩ intLattice d).Nonempty)
    (hzero : Module.finrank ℝ (affZ I).direction = 0) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty := by
  obtain ⟨z, hzI, hzZ⟩ := hZ
  have hzF : z ∈ affZ I := mem_affineSpan ℝ ⟨hzI, hzZ⟩
  have hf : ∀ w ∈ affZ I, w = z := by
    intro w hw
    have hwz : w - z ∈ (affZ I).direction := AffineSubspace.vsub_mem_direction hw hzF
    let : Subsingleton (affZ I).direction := Module.finrank_zero_iff.mp hzero
    have h : (⟨w-z,hwz⟩ : (affZ I).direction) = 0 := Subsingleton.elim _ _
    exact sub_eq_zero.mp (congrArg Subtype.val h)
  have he : IZ I = {z} := by
    ext w
    constructor
    · intro hw
      exact hf w hw.2
    · rintro rfl
      exact ⟨hzI,hzF⟩
  rw [he, intrinsicInterior_singleton]
  exact ⟨z,rfl,hzZ⟩

lemma affine_rank_preserved {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty)
    (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ) (hA : IsUnit A)
    (himage : ratAff A b '' intLattice d = intLattice d)
    (hpre : ratAff A b ⁻¹' intLattice d = intLattice d) :
    Module.finrank ℝ (affZ (ratAff A b '' I)).direction =
      Module.finrank ℝ (affZ I).direction := by
  have him := ((lemma_6_3 I hI hZ).2.2.2.2 A b hA himage hpre).2
  have he : (affZ I).map (DecompositionChange.affineMap A b) = affZ (ratAff A b '' I) := by
    apply SetLike.coe_injective
    exact him
  rw [← he, AffineSubspace.map_direction]
  have hAR : IsUnit (A.map (fun q : ℚ => (q : ℝ))) := hA.map (Rat.castHom ℝ).mapMatrix
  let e := Matrix.toLinearEquiv' (A.map (fun q : ℚ => (q : ℝ))) hAR.invertible
  have helinear : (DecompositionChange.affineMap A b).linear = e.toLinearMap := by
    ext z i
    simp [DecompositionChange.affineMap, e]
  rw [helinear]
  exact e.finrank_map_eq (affZ I).direction

lemma empty_binary {n : ℕ} : IsBinaryMICPR (∅ : Set (Pt n)) := by
  refine ⟨0,0,∅,⟨isClosed_empty,convex_empty,?_⟩,?_⟩
  · intro x
    simp
  · simp

end MICPRep.Periodic.DecompositionProof


namespace MICPRep.Periodic.DecompositionProof

open scoped ENNReal Matrix

/-- A finite decomposition using the original numbers of auxiliary and integer variables. -/
def GoodDecomposition {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n)) : Prop :=
  ∃ (k : ℕ) (Ms : Fin k → Set (Ambient n p d)) (Ss : Fin k → Set (Pt n)),
    (∀ i, IsRationalFormulation (Ms i) (Ss i) ∧ (Ss i).Nonempty ∧
      micpDiam (Ms i) ≤ micpDiam M ∧
      (intrinsicInterior ℝ (IZ (indexSet (Ms i))) ∩ intLattice d).Nonempty) ∧
    S = ⋃ i, Ss i

lemma empty_decomposition {n p d : ℕ} (M : Set (Ambient n p d)) :
    GoodDecomposition M (∅ : Set (Pt n)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, ?_⟩
  simp

lemma singleton_decomposition {n p d : ℕ} {M : Set (Ambient n p d)} {S : Set (Pt n)}
    (hM : IsRationalFormulation M S) (hS : S.Nonempty)
    (hgood : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty) :
    GoodDecomposition M S := by
  refine ⟨1,fun _ => M,fun _ => S,fun _ => ⟨hM,hS,le_rfl,hgood⟩,?_⟩
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨0,hx⟩
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact hi

lemma combine_decompositions {n p d t : ℕ} (M : Set (Ambient n p d))
    (Ms : Fin t → Set (Ambient n p d)) (Ss : Fin t → Set (Pt n))
    (hdiam : ∀ i, micpDiam (Ms i) ≤ micpDiam M)
    (hgood : ∀ i, GoodDecomposition (Ms i) (Ss i)) :
    GoodDecomposition M (⋃ i, Ss i) := by
  classical
  choose k Ns Ts hN hcover using hgood
  let J := (i : Fin t) × Fin (k i)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,fun j => Ns (e j).1 (e j).2,
    fun j => Ts (e j).1 (e j).2,?_,?_⟩
  · intro j
    obtain ⟨hR,hne,hd,hi⟩ := hN (e j).1 (e j).2
    exact ⟨hR,hne,hd.trans (hdiam (e j).1),hi⟩
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      rw [hcover i] at hi
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
      refine ⟨e.symm ⟨i,j⟩, ?_⟩
      rw [e.apply_symm_apply]
      exact hj
    · rintro ⟨j,hj⟩
      refine ⟨(e j).1,?_⟩
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨(e j).2,hj⟩

end MICPRep.Periodic.DecompositionProof


namespace MICPRep.Periodic.DecompositionProof

open scoped ENNReal Matrix
set_option maxHeartbeats 1600000

/-- Exactly the unresolved registered Lemma 6.5, passed as an explicit proposition. -/
def SlabDichotomy : Prop :=
  ∀ {d : ℕ} (I : Set (Fin d → ℝ)), Convex ℝ I → (I ∩ intLattice d).Nonempty →
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty ∨
    ∃ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A ∧
      ratAff A b '' intLattice d = intLattice d ∧
      ratAff A b ⁻¹' intLattice d = intLattice d ∧
      ∃ l u : ℤ, IZ (ratAff A b '' I) ⊆ slab d l u ∧
        (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) = coordSubspace d (setDim (IZ I))

lemma normalize {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty)
    (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ) (hA : IsUnit A)
    (himage : ratAff A b '' intLattice d = intLattice d)
    (hpre : ratAff A b ⁻¹' intLattice d = intLattice d) :
    ∃ N : Set (Ambient n p d), IsRationalFormulation N S ∧
      indexSet N = ratAff A b '' indexSet M ∧ micpDiam N ≤ micpDiam M ∧
      Module.finrank ℝ (affZ (indexSet N)).direction =
        Module.finrank ℝ (affZ (indexSet M)).direction := by
  obtain ⟨hN, hindex, hdiam, heq⟩ := lemma_6_6 M S hM A b hA hpre.le
  obtain ⟨hS', _⟩ := heq himage hpre
  rw [hS'] at hN
  refine ⟨_,hN,hindex,hdiam,?_⟩
  rw [hindex]
  exact affine_rank_preserved (indexSet M) (convex_index hM.1.2.1)
    (lattice_index_nonempty hM.1 hS) A b hA himage hpre

lemma split_bad (hslab : SlabDichotomy) {n p d : ℕ}
    (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty)
    (hbad : ¬ (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty) :
    ∃ (t : ℕ) (Ns : Fin t → Set (Ambient n p d)) (Ts : Fin t → Set (Pt n)),
      (∀ i, IsRationalFormulation (Ns i) (Ts i)) ∧ S = ⋃ i, Ts i ∧
      ∀ i, micpDiam (Ns i) ≤ micpDiam M ∧
        ((Ts i).Nonempty → Module.finrank ℝ (affZ (indexSet (Ns i))).direction <
          Module.finrank ℝ (affZ (indexSet M)).direction) := by
  classical
  have hI := convex_index hM.1.2.1
  have hZ := lattice_index_nonempty hM.1 hS
  obtain hgood | ⟨A,b,hA,himage,hpre,l,u,hslab',hcoord⟩ := hslab (indexSet M) hI hZ
  · exact (hbad hgood).elim
  obtain ⟨N,hN,hidx,hdiam,hrank⟩ := normalize M S hM hS A b hA himage hpre
  have hZN := lattice_index_nonempty hN.1 hS
  have hFN := affine_integer_nonempty hZN
  have hFM := affine_integer_nonempty hZ
  have hdim : affDim (affZ (indexSet N)) = affDim (affZ (indexSet M)) := by
    simp only [affDim, if_pos hFN, if_pos hFM, hrank]
  have hd0 : Module.finrank ℝ (affZ (indexSet M)).direction ≠ 0 := by
    intro hz
    exact hbad (rank_zero_good hZ hz)
  have hpos : 1 ≤ affDim (affZ (indexSet N)) := by
    rw [hdim]
    simp only [affDim, if_pos hFM]
    omega
  have hsetdim : setDim (IZ (indexSet M)) = affDim (affZ (indexSet M)) := by
    unfold setDim
    rw [← (lemma_6_3 (indexSet M) hI hZ).2.2.2.1]
  have hcoordN : (affZ (indexSet N) : Set (Fin d → ℝ)) =
      coordSubspace d (affDim (affZ (indexSet N))) := by
    rw [← hidx, hsetdim] at hcoord
    rw [hdim]
    exact hcoord
  have hslabN : IZ (indexSet N) ⊆ slab d l u := by simpa only [hidx] using hslab'
  obtain ⟨C,c,hC,hdrop,hcover,hfix⟩ :=
    lemma_6_7 l u (indexSet N) (convex_index hN.1.2.1) hcoordN hslabN hpos
  let J := {i : ℤ // i ∈ Finset.Icc l u}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let Ns : Fin (Fintype.card J) → Set (Ambient n p d) := fun i =>
    {q | (q.1,q.2.1,ratAffInv (C (e i)) (c (e i)) q.2.2) ∈ N}
  let Ts : Fin (Fintype.card J) → Set (Pt n) := fun i =>
    ⋃ z ∈ ratAff (C (e i)) (c (e i)) '' indexSet N ∩ intLattice d,
      zProj N (ratAffInv (C (e i)) (c (e i)) z)
  have hei (i : Fin (Fintype.card J)) : (e i).val ∈ Set.Icc l u := by
    simpa only [Finset.mem_Icc, Set.mem_Icc] using (e i).property
  have htrans (i : Fin (Fintype.card J)) : IsRationalFormulation (Ns i) (Ts i) ∧
      indexSet (Ns i) = ratAff (C (e i)) (c (e i)) '' indexSet N ∧
      micpDiam (Ns i) ≤ micpDiam N := by
    apply DecompositionChange.transform N S hN (C (e i)) (c (e i)) (hC _ (hei i))
    intro z hz
    rw [hfix _ (hei i) z hz]
    exact hz.2
  refine ⟨Fintype.card J,Ns,Ts,fun i => (htrans i).1,?_,?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y,z,hz,hm⟩ := (hN.1.2.2 x).mp hx
      have hzI : z ∈ indexSet N ∩ intLattice d := ⟨⟨(x,y,z),hm,rfl⟩,hz⟩
      rw [← hcover] at hzI
      obtain ⟨i,hi,hzi⟩ := Set.mem_iUnion₂.mp hzI
      let j : J := ⟨i,by simpa only [Finset.mem_Icc, Set.mem_Icc] using hi⟩
      refine Set.mem_iUnion.mpr ⟨e.symm j,?_⟩
      change x ∈ ⋃ z ∈ ratAff (C (e (e.symm j))) (c (e (e.symm j))) '' indexSet N ∩
        intLattice d, zProj N (ratAffInv (C (e (e.symm j))) (c (e (e.symm j))) z)
      simp only [Equiv.apply_symm_apply]
      apply Set.mem_iUnion₂.mpr
      refine ⟨z,hzi,?_⟩
      rw [hfix i hi z hzi]
      exact ⟨y,hm⟩
    · intro hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨z,hz,hy⟩ := Set.mem_iUnion₂.mp hi
      rw [hfix _ (hei i) z hz] at hy
      obtain ⟨y,hm⟩ := hy
      exact (hN.1.2.2 x).mpr ⟨y,z,hz.2,hm⟩
  · intro i
    refine ⟨(htrans i).2.2.trans hdiam,?_⟩
    intro hTi
    have hFi := affine_integer_nonempty (lattice_index_nonempty (htrans i).1.1 hTi)
    have hd := hdrop (e i) (hei i)
    rw [← (htrans i).2.1, hdim] at hd
    simp only [affDim, if_pos hFi, if_pos hFM] at hd
    omega

end MICPRep.Periodic.DecompositionProof


namespace MICPRep.Periodic.DecompositionProof

set_option maxHeartbeats 800000

lemma decomposition (hslab : SlabDichotomy) {n p d : ℕ}
    (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) :
    GoodDecomposition M S := by
  classical
  have aux : ∀ q : ℕ, ∀ (M : Set (Ambient n p d)) (S : Set (Pt n)),
      IsRationalFormulation M S → S.Nonempty →
      Module.finrank ℝ (affZ (indexSet M)).direction = q → GoodDecomposition M S := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro M S hM hS hq
      by_cases hgood : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty
      · exact singleton_decomposition hM hS hgood
      obtain ⟨t,Ns,Ts,hR,hcover,hprops⟩ := split_bad hslab M S hM hS hgood
      have hchild : ∀ i, GoodDecomposition (Ns i) (Ts i) := by
        intro i
        by_cases hi : (Ts i).Nonempty
        · apply ih (Module.finrank ℝ (affZ (indexSet (Ns i))).direction) _
            (Ns i) (Ts i) (hR i) hi rfl
          rw [← hq]
          exact (hprops i).2 hi
        · rw [Set.not_nonempty_iff_eq_empty.mp hi]
          exact empty_decomposition (Ns i)
      rw [hcover]
      exact combine_decompositions M Ns Ts (fun i => (hprops i).1) hchild
  exact aux _ M S hM hS rfl

end MICPRep.Periodic.DecompositionProof

open MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.1, p. 21. -/
theorem conditional_solution (hslab : DecompositionProof.SlabDichotomy) {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) :
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (Ms : Fin k → Set (Ambient n p d)) (Ss : Fin k → Set (Pt n)),
        (∀ i, IsRationalFormulation (Ms i) (Ss i) ∧ (Ss i).Nonempty) ∧
        S = S₀ ∪ ⋃ i, Ss i ∧
        ∀ i, micpDiam (Ms i) ≤ micpDiam M ∧
          (intrinsicInterior ℝ (IZ (indexSet (Ms i))) ∩ intLattice d).Nonempty := by
  obtain ⟨k,Ms,Ss,hpieces,hcover⟩ := DecompositionProof.decomposition hslab M S hM hS
  refine ⟨∅,DecompositionProof.empty_binary,k,Ms,Ss,?_,?_,?_⟩
  · intro i
    exact ⟨(hpieces i).1,(hpieces i).2.1⟩
  · simpa only [Set.empty_union] using hcover
  · intro i
    exact (hpieces i).2.2


open MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.1, p. 21. -/
theorem solution {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) :
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (Ms : Fin k → Set (Ambient n p d)) (Ss : Fin k → Set (Pt n)),
        (∀ i, IsRationalFormulation (Ms i) (Ss i) ∧ (Ss i).Nonempty) ∧
        S = S₀ ∪ ⋃ i, Ss i ∧
        ∀ i, micpDiam (Ms i) ≤ micpDiam M ∧
          (intrinsicInterior ℝ (IZ (indexSet (Ms i))) ∩ intLattice d).Nonempty := by
  exact conditional_solution MICPRep.Periodic.lemma_6_5 M S hM hS


-- Prove2me | solution 1 for OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:44:01.490991+00:00
-- url     : https://prove2.me/submissions/01e005b9-6aba-4199-9f10-316cee3609b2

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_exponential_coarsePair_bound

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Paths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem pathCost_append (τ : Edge → ℝ) (p : Vertex) (ds es : List Step) :
    pathCost τ p (ds ++ es) =
      pathCost τ p ds + pathCost τ (p + displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, add_assoc]

theorem pathCost_nonneg {τ : Edge → ℝ} (hτ : ∀ e, 0 ≤ τ e)
    (p : Vertex) (ds : List Step) : 0 ≤ pathCost τ p ds := by
  induction ds generalizing p with
  | nil => exact le_refl 0
  | cons d ds ih => exact add_nonneg (hτ _) (ih _)

theorem defect_append (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds es : List Step) :
    defect τ b m a p (ds ++ es) =
      defect τ b m a p ds + defect τ b m a (p + displacement ds) es := by
  simp [defect, pathCost_append]; ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PassageTime
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem displacement_vertical (n : ℤ) : displacement (vertical n) = (0, n) := by
  by_cases hn : 0 ≤ n
  · simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CoordinateTails
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem straightEdge_injective (p : Vertex) (d : Step) :
    Function.Injective (straightEdge p d) := by
  intro i j h
  cases d <;> simp [straightEdge, Step.edge, Step.delta, Prod.ext_iff] at h <;> omega

theorem pathCost_replicate (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ i ∈ range n, w (straightEdge p d i) := by
  induction n generalizing p with
  | zero => simp [pathCost]
  | succ n ih =>
    rw [List.replicate_succ, pathCost, ih, sum_range_succ']
    simp [straightEdge, Nat.cast_add, add_smul, add_assoc, add_comm]

theorem pathCost_replicate_edgeSet (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ e ∈ (range n).image (straightEdge p d), w e := by
  rw [sum_image (fun i _ j _ hij => straightEdge_injective p d hij)]
  exact pathCost_replicate w p d n

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathConcatenation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

theorem exists_path_chain (w : Edge → ℝ) (p : ℕ → Vertex) (S : Set Vertex)
    (a : ℕ → ℝ) (n : ℕ) (hp : p 0 ∈ S)
    (h : ∀ i < n, ∃ ds, p i+displacement ds=p (i+1) ∧
      pathCost w (p i) ds ≤ a i ∧ PathIn (p i) ds S) :
    ∃ ds, p 0+displacement ds=p n ∧
      pathCost w (p 0) ds ≤ ∑ i ∈ range n, a i ∧ PathIn (p 0) ds S := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp [pathCost],?_⟩
    intro i hi
    simpa using hp
  | succ n ih =>
    obtain ⟨ds,hd,hcostd,hind⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨es,he,hcoste,hine⟩ := h n (Nat.lt_succ_self n)
    refine ⟨ds++es,?_,?_,?_⟩
    · rw [displacement_append, ← add_assoc, hd]
      exact he
    · rw [pathCost_append, hd, sum_range_succ]
      exact add_le_add hcostd hcoste
    · apply pathIn_append _ _ _ _ hind
      simpa only [hd] using hine

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFastEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SourceTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridMeshes
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set MeasureTheory
open scoped Topology

lemma gridMesh_pos (m j : ℕ) : 0 < gridMesh m j := by unfold gridMesh; positivity
lemma gridWidth_pos (k j : ℕ) : 0 < gridWidth k j := by unfold gridWidth; positivity
lemma gridLastLevel_unit (m : ℕ) : gridMesh m (gridLastLevel m)=1 := by
  have he : gridMeshExponent m (gridLastLevel m)=0 := by
    unfold gridMeshExponent gridLastLevel
    omega
  simp [gridMesh,he]

lemma gridMesh_antitone (m : ℕ) : Antitone (gridMesh m) := by
  intro i j hij
  apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
  unfold gridMeshExponent
  omega

lemma gridMesh_ratio_le (m j : ℕ) : gridMesh m j ≤ 16*gridMesh m (j+1) := by
  have he : gridMeshExponent m j ≤ 4+gridMeshExponent m (j+1) := by unfold gridMeshExponent; omega
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he
  simpa [gridMesh,pow_add] using hh

lemma gridMesh_divides (m j : ℕ) : gridMesh m (j+1) ∣ gridMesh m j := by
  apply pow_dvd_pow
  unfold gridMeshExponent
  omega

lemma gridMesh_count_ratio (m j : ℕ) :
    (2 : ℝ)^m / (gridMesh m j : ℝ) ≤ (2 : ℝ)^(4*j+1) := by
  have hg : (0 : ℝ) < (gridMesh m j : ℝ) := by exact_mod_cast gridMesh_pos m j
  rw [div_le_iff₀ hg]
  simp only [gridMesh,Int.cast_pow,Int.cast_ofNat,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  unfold gridMeshExponent
  omega

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointMesh
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

lemma meshFloor_bounds (x d : ℤ) (hd : 0 < d) :
    meshFloor x d ≤ x ∧ x < meshFloor x d+d := by
  have h0 := Int.emod_nonneg x (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos x hd
  have he := Int.emod_add_ediv_mul x d
  dsimp [meshFloor]
  omega

lemma meshFloor_dvd (x d : ℤ) : d ∣ meshFloor x d := by
  exact ⟨x/d,by simp [meshFloor,mul_comm]⟩

lemma meshFloor_greatest (x d y : ℤ) (hd : 0 < d) (hy : y ≤ x) (hdy : d ∣ y) :
    y ≤ meshFloor x d := by
  obtain ⟨z,rfl⟩ := hdy
  have hz : z ≤ x/d := (Int.le_ediv_iff_mul_le hd).mpr (by simpa [mul_comm] using hy)
  exact (show d*z ≤ x/d*d by nlinarith)

lemma meshFloor_refinement (x d D : ℤ) (hd : 0 < d) (hD : 0 < D) (hdD : d ∣ D) :
    meshFloor x D ≤ meshFloor x d ∧ meshFloor x d-meshFloor x D < D := by
  have hb := meshFloor_bounds x D hD
  have hb' := meshFloor_bounds x d hd
  exact ⟨meshFloor_greatest x d _ hd hb.1 (dvd_trans hdD (meshFloor_dvd x D)),by omega⟩

theorem meshFloor_refinement_count (x d D : ℤ) (hd : 0 < d) (hD : 0 < D)
    (hdD : d ∣ D) (hratio : D ≤ 16*d) :
    ∃ n : ℕ, n < 16 ∧ meshFloor x D+(n : ℤ)*d=meshFloor x d := by
  have hb := meshFloor_refinement x d D hd hD hdD
  have hdiv : d ∣ meshFloor x d-meshFloor x D :=
    dvd_sub (meshFloor_dvd x d) (dvd_trans hdD (meshFloor_dvd x D))
  obtain ⟨z,hz⟩ := hdiv
  have hz0 : 0 ≤ z := by nlinarith [hb.1]
  have hz16 : z < 16 := by nlinarith [hb.2]
  refine ⟨z.toNat,by omega,?_⟩
  rw [Int.toNat_of_nonneg hz0]
  nlinarith

lemma endpointColumn_last (x : ℤ) (m : ℕ) :
    endpointColumn x m (gridLastLevel m)=x := by
  simp [endpointColumn,gridLastLevel_unit,meshFloor]

lemma endpointColumn_step (x : ℤ) (m j : ℕ) :
    ∃ n : ℕ, n < 16 ∧ endpointColumn x m j+(n : ℤ)*gridMesh m (j+1)=
      endpointColumn x m (j+1) :=
  meshFloor_refinement_count x _ _ (gridMesh_pos m (j+1)) (gridMesh_pos m j)
    (gridMesh_divides m j) (gridMesh_ratio_le m j)

lemma gridMesh_dvd_of_le (m i j : ℕ) (hij : i ≤ j) : gridMesh m j ∣ gridMesh m i := by
  apply pow_dvd_pow
  unfold gridMeshExponent
  omega

lemma endpointColumn_mono (x : ℤ) (m : ℕ) : Monotone (endpointColumn x m) := by
  intro i j hij
  exact meshFloor_greatest x _ _ (gridMesh_pos m j)
    (meshFloor_bounds x _ (gridMesh_pos m i)).1
    (dvd_trans (gridMesh_dvd_of_le m i j hij) (meshFloor_dvd x _))

lemma entranceColumn_span (x : ℤ) (m J : ℕ) :
    gridMesh m J ≤ x-entranceColumn x m J ∧
      x-entranceColumn x m J < 2*gridMesh m J := by
  have hb := meshFloor_bounds x (gridMesh m J) (gridMesh_pos m J)
  dsimp [entranceColumn,endpointColumn]
  omega

lemma exitColumn_span (x : ℤ) (m J : ℕ) :
    gridMesh m J ≤ exitColumn x m J-x ∧
      exitColumn x m J-x < 2*gridMesh m J := by
  have hb := entranceColumn_span (-x) m J
  dsimp [exitColumn]
  omega

lemma entranceColumn_dvd (x : ℤ) (m J : ℕ) : gridMesh m J ∣ entranceColumn x m J :=
  dvd_sub (meshFloor_dvd x _) (dvd_refl _)

lemma exitColumn_dvd (x : ℤ) (m J : ℕ) : gridMesh m J ∣ exitColumn x m J :=
  dvd_neg.mpr (entranceColumn_dvd (-x) m J)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

lemma endpointVertex_error (b r : ℝ) (X : ℤ) :
    -1 < transverse b (endpointVertex b r X)-r ∧
      transverse b (endpointVertex b r X)-r ≤ 0 := by
  have hl := Int.floor_le (b*X+r)
  have hu := Int.lt_floor_add_one (b*X+r)
  dsimp [transverse,endpointVertex]
  constructor <;> linarith

lemma endpointVertex_close (b r : ℝ) (X : ℤ) :
    |transverse b (endpointVertex b r X)-r| < 1 := by
  have h := endpointVertex_error b r X
  exact abs_lt.mpr ⟨h.1,by linarith [h.2]⟩

lemma endpointVertex_self (b : ℝ) (p : Vertex) :
    endpointVertex b (transverse b p) p.1=p := by
  apply Prod.ext
  · rfl
  · simp [endpointVertex,transverse]

lemma endpointVertex_displacement (b r : ℝ) (X Y : ℤ) :
    |transverse b (endpointVertex b r Y-endpointVertex b r X)| < 1 := by
  have hx := endpointVertex_error b r X
  have hy := endpointVertex_error b r Y
  have he : transverse b (endpointVertex b r Y-endpointVertex b r X) =
      transverse b (endpointVertex b r Y)-transverse b (endpointVertex b r X) := by
    simp [transverse]; ring
  rw [he,abs_lt]
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

lemma endpoint_path_defect (w : Edge → ℝ) (b r m₀ a E : ℝ) (X Y : ℤ)
    (ds : List Step)
    (hd : endpointVertex b r X+displacement ds=endpointVertex b r Y)
    (hc : pathCost w (endpointVertex b r X) ds ≤ m₀*((Y-X : ℤ) : ℝ)+E) :
    defect w b m₀ a (endpointVertex b r X) ds ≤ E+|a| := by
  have hd' : displacement ds=endpointVertex b r Y-endpointVertex b r X := by
    rw [← hd]; abel
  have hr := (endpointVertex_displacement b r X Y).le
  have hm : |a*transverse b (endpointVertex b r Y-endpointVertex b r X)| ≤ |a| := by
    rw [abs_mul]
    nlinarith [abs_nonneg a]
  have hlo := (abs_le.mp hm).1
  unfold defect support
  rw [hd']
  have hx : (endpointVertex b r Y-endpointVertex b r X).1=Y-X := rfl
  rw [hx]
  linarith

lemma negative_defect_reverse_span (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a R s ε : ℝ) (hm : 0 < m₀) (_hR : 0 ≤ R) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (p z : Vertex) (ds : List Step) (hd : p+displacement ds=z)
    (hp : |transverse b p| ≤ R*s) (hz : |transverse b z| ≤ R*s)
    (hc : defect w b m₀ a p ds < -ε*s) :
    -2*R*|a| *s/m₀ ≤ ((z.1-p.1 : ℤ) : ℝ) := by
  have hd' : displacement ds=z-p := by rw [← hd]; abel
  have hr : |transverse b (z-p)| ≤ 2*R*s := by
    have he : transverse b (z-p)=transverse b z-transverse b p := by simp [transverse]; ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have ha : a*transverse b (z-p) ≤ 2*R*|a| *s := by
    have hh := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
    have hb := le_abs_self (a*transverse b (z-p))
    rw [abs_mul] at hb
    nlinarith
  have hcost := pathCost_nonneg hw p ds
  have heps := mul_nonneg hε hs
  unfold defect support at hc
  rw [hd'] at hc
  change pathCost w p ds-(m₀*((z.1-p.1 : ℤ) : ℝ)+a*transverse b (z-p)) < -ε*s at hc
  apply (div_le_iff₀ hm).mpr
  nlinarith

lemma extended_columns_span (p z : ℤ) (m J : ℕ) (C s : ℝ)
    (hrev : -C*s ≤ ((z-p : ℤ) : ℝ))
    (hscale : C*s ≤ (gridMesh m J : ℝ)) :
    (gridMesh m J : ℝ) ≤ ((exitColumn z m J-entranceColumn p m J : ℤ) : ℝ) := by
  have hp := entranceColumn_span p m J
  have hz := exitColumn_span z m J
  have hp' : (gridMesh m J : ℝ) ≤ ((p-entranceColumn p m J : ℤ) : ℝ) := by exact_mod_cast hp.1
  have hz' : (gridMesh m J : ℝ) ≤ ((exitColumn z m J-z : ℤ) : ℝ) := by exact_mod_cast hz.1
  push_cast at hp' hz' hrev ⊢
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointTail
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Finset
open scoped Topology

lemma endpointErrorTerm_nonneg (j : ℕ) : 0 ≤ endpointErrorTerm j := by
  unfold endpointErrorTerm
  positivity

lemma summable_endpointErrorTerm : Summable endpointErrorTerm := by
  exact summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1/2 : ℝ)‖ < 1)

lemma endpointErrorTail_tendsto : Tendsto endpointErrorTail atTop (𝓝 0) :=
  tendsto_sum_nat_add endpointErrorTerm

lemma endpointErrorTerm_le_two (j : ℕ) : endpointErrorTerm j ≤ 2 := by
  have h (n : ℕ) : (n : ℝ)^2 ≤ 2*(2 : ℝ)^n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 4
      · interval_cases n <;> norm_num
      · obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
        have ha : (3 : ℝ) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
        have hb := ih a (by omega)
        simp only [Nat.cast_add,Nat.cast_one,pow_add,pow_one]
        nlinarith
  have hp := mul_le_mul_of_nonneg_right (h j) (show 0 ≤ (1/2 : ℝ)^j by positivity)
  have he : (2 : ℝ)^j*(1/2 : ℝ)^j=1 := by rw [← mul_pow]; norm_num
  unfold endpointErrorTerm
  nlinarith

lemma gridWidth_endpointError (k j : ℕ) (hj : j ≤ k) :
    (j : ℝ)^2*(gridWidth k j : ℝ)=(2 : ℝ)^k*endpointErrorTerm j := by
  have he : (2 : ℝ)^k=(2 : ℝ)^(k-j)*(2 : ℝ)^j := by rw [← pow_add,Nat.sub_add_cancel hj]
  have hc : (2 : ℝ)^j*(1/2 : ℝ)^j=1 := by rw [← mul_pow]; norm_num
  simp only [endpointErrorTerm,gridWidth,Int.cast_pow,Int.cast_ofNat]
  rw [he]
  calc
    _ = (2 : ℝ)^(k-j)*(j : ℝ)^2*((2 : ℝ)^j*(1/2 : ℝ)^j) := by rw [hc]; ring
    _ = _ := by ring

lemma endpointError_sum_le_tail (J n : ℕ) :
    (∑ i ∈ range n,endpointErrorTerm (J+i)) ≤ endpointErrorTail J := by
  have hs : Summable (fun i : ℕ => endpointErrorTerm (i+J)) := summable_endpointErrorTerm.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  simpa [endpointErrorTail,Nat.add_comm] using
    hs.sum_le_tsum (range n) (fun i _ => endpointErrorTerm_nonneg (i+J))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointBounds
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

lemma gridMesh_le_scale (m j : ℕ) : (gridMesh m j : ℝ) ≤ (2 : ℝ)^m := by
  simp only [gridMesh,Int.cast_pow,Int.cast_ofNat]
  apply pow_le_pow_right₀ (by norm_num)
  unfold gridMeshExponent
  omega

lemma grid_endpoint_height (K : ℝ) (hK : 0 ≤ K) (k j : ℕ) (hj : j ≤ k) :
    (K+200)*(j : ℝ)^2*gridWidth k j ≤ 2*(K+200)*(2 : ℝ)^k := by
  have h := mul_le_mul_of_nonneg_left (endpointErrorTerm_le_two j)
    (show 0 ≤ (K+200)*(2 : ℝ)^k by positivity)
  rw [mul_assoc,gridWidth_endpointError k j hj]
  nlinarith

lemma endpoint_extension_cost_sum (K : ℝ) (hK : 0 ≤ K) (k m J : ℕ)
    (hlast : gridLastLevel m ≤ k) (hJ : J ≤ gridLastLevel m) :
    (∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i))) ≤
      endpointExtensionError K k J := by
  have heq : (∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i))) =
      16*(K+200)*(2 : ℝ)^k*(∑ i ∈ range (gridLastLevel m-J+1),endpointErrorTerm (J+i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hj : J+i ≤ k := by omega
    have hh := gridWidth_endpointError k (J+i) hj
    calc
      _ = 16*(K+200)*(((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)) := by ring
      _ = _ := by rw [hh]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (endpointError_sum_le_tail J _ ) (by positivity)

lemma endpoint_localization (b A R C : ℝ) (_hC : 0 ≤ C) (k m : ℕ) (p z : Vertex) (d : ℤ)
    (hd : (d : ℝ) ≤ (2 : ℝ)^m)
    (hp : |(p.1 : ℝ)| ≤ A*(2 : ℝ)^m) (hr : |transverse b p| ≤ R*(2 : ℝ)^k)
    (hx : p.1-3*d ≤ z.1 ∧ z.1 ≤ p.1+3*d)
    (hz : |transverse b z-transverse b p| ≤ 2*C*(2 : ℝ)^k) :
    |(z.1 : ℝ)| ≤ (A+4)*(2 : ℝ)^m ∧
      |transverse b z| ≤ (R+2*C)*(2 : ℝ)^k := by
  have hx' : (p.1 : ℝ)-3*(d : ℝ) ≤ (z.1 : ℝ) ∧
      (z.1 : ℝ) ≤ (p.1 : ℝ)+3*(d : ℝ) := by exact_mod_cast hx
  have hp' := abs_le.mp hp
  refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩
  · linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]
  · linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]
  · have hh := abs_add_le (transverse b z-transverse b p) (transverse b p)
    rw [sub_add_cancel] at hh
    linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridCounting
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set

lemma mem_gridIndexRange_of_abs_le (x : ℝ) (i : ℤ) (hi : |(i : ℝ)| ≤ x) :
    i ∈ gridIndexRange x := by
  have hn := hi.trans (Nat.le_ceil x)
  have hn' : |i| ≤ (⌈x⌉₊ : ℤ) := by exact_mod_cast hn
  exact Finset.mem_Icc.mpr (abs_le.mp hn')

lemma grid_interval_index_mem (A R L s : ℝ) (l w : ℤ) (hl : 0 < l) (hw : 0 < w)
    (i : ℤ) (r₀ : ℝ)
    (hi : -(A+4)*L ≤ ((l*i : ℤ) : ℝ) ∧ ((l*i : ℤ) : ℝ) ≤ (A+4)*L)
    (hr : |r₀| ≤ R*s) :
    (i,⌊r₀/(w : ℝ)⌋) ∈ gridTestIndices A R L s l w := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  apply Finset.mem_product.mpr
  constructor
  · apply mem_gridIndexRange_of_abs_le
    rw [le_div_iff₀ hl']
    have hh : |((l*i : ℤ) : ℝ)| ≤ (A+4)*L := abs_le.mpr (by simpa only [neg_mul] using hi)
    rw [Int.cast_mul,abs_mul,abs_of_pos hl'] at hh
    nlinarith
  · apply mem_gridIndexRange_of_abs_le
    have hf := Int.floor_le (r₀/(w : ℝ))
    have hf' := Int.lt_floor_add_one (r₀/(w : ℝ))
    have hr' : |r₀/(w : ℝ)| ≤ R*s/w := by
      rw [abs_div,abs_of_pos hw']
      exact div_le_div_of_nonneg_right hr hw'.le
    have hh := abs_le.mp hr'
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2]

lemma grid_bin_floor (w : ℤ) (hw : 0 < w) (r : ℝ) :
    (⌊r/(w : ℝ)⌋ : ℝ)*w ≤ r ∧ r ≤ ((⌊r/(w : ℝ)⌋ : ℝ)+1)*w := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  exact ⟨(le_div_iff₀ hw').mp (Int.floor_le _),
    ((div_lt_iff₀ hw').mp (Int.lt_floor_add_one _)).le⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridTrials
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma gridTrialTranslate_center (b : ℝ) (X h w : ℤ) (t : ℕ) :
    transverse b (gridTrialTranslate b X h w t) =
      (⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w := by
  simp [gridTrialTranslate,transverse]
  ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_VerticalIntervals
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma vertical_straight_subset (X lo hi y : ℤ) (d : Step) (n : ℕ)
    (hd : d=.north ∨ d=.south)
    (hy : lo ≤ y ∧ y ≤ hi)
    (hz : lo ≤ y+(n : ℤ)*d.delta.2 ∧ y+(n : ℤ)*d.delta.2 ≤ hi) :
    (Finset.range n).image (straightEdge (X,y) d) ⊆ verticalIntervalEdges X lo hi := by
  intro e he
  obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp he
  have hi'' := Finset.mem_range.mp hi'
  rcases hd with rfl | rfl
  · refine Finset.mem_image.mpr ⟨y+i,Finset.mem_Ico.mpr ?_,?_⟩
    · simp only [Step.delta] at hz
      constructor <;> omega
    · simp [straightEdge,Step.edge,Step.delta]
  · refine Finset.mem_image.mpr ⟨y-(i : ℤ)-1,Finset.mem_Ico.mpr ?_,?_⟩
    · simp only [Step.delta] at hz
      constructor <;> omega
    · simp [straightEdge,Step.edge,Step.delta,Prod.ext_iff]
      omega

lemma vertical_straight_in (X lo hi y : ℤ) (d : Step) (n : ℕ)
    (hd : d=.north ∨ d=.south)
    (hy : lo ≤ y ∧ y ≤ hi)
    (hz : lo ≤ y+(n : ℤ)*d.delta.2 ∧ y+(n : ℤ)*d.delta.2 ≤ hi) :
    PathIn (X,y) (List.replicate n d) {p | p.1=X ∧ lo ≤ p.2 ∧ p.2 ≤ hi} := by
  intro i hi'
  have hi'' : i ≤ n := by simpa using hi'
  have htake : (List.replicate n d).take i = List.replicate i d := by
    simp [List.take_replicate,Nat.min_eq_left hi'']
  rw [htake]
  simp only [displacement,List.map_replicate,List.sum_replicate]
  rcases hd with rfl | rfl <;>
    simp [Step.delta,Prod.smul_mk] at hz ⊢ <;> omega

theorem vertical_interval_all_pairs (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (X lo hi : ℤ) (p q : Vertex) (hp : p.1=X ∧ lo ≤ p.2 ∧ p.2 ≤ hi)
    (hq : q.1=X ∧ lo ≤ q.2 ∧ q.2 ≤ hi) :
    ∃ ds, p+displacement ds=q ∧
      pathCost w p ds ≤ ∑ e ∈ verticalIntervalEdges X lo hi,w e ∧
      PathIn p ds {z | z.1=X ∧ lo ≤ z.2 ∧ z.2 ≤ hi} := by
  have hp' : p=(X,p.2) := Prod.ext hp.1 rfl
  have hq' : q=(X,q.2) := Prod.ext hq.1 rfl
  let ds := vertical (q.2-p.2)
  refine ⟨ds,?_,?_,?_⟩
  · simp [ds,displacement_vertical,Prod.ext_iff,hp.1,hq.1]
  · by_cases hle : p.2 ≤ q.2
    · have hn : (((q.2-p.2).toNat : ℕ) : ℤ)=q.2-p.2 := Int.toNat_of_nonneg (by omega)
      rw [show ds=List.replicate (q.2-p.2).toNat Step.north by simp [ds,vertical,hle],
        hp',pathCost_replicate_edgeSet]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply vertical_straight_subset X lo hi p.2 .north _ (Or.inl rfl) hp.2
        simpa only [Step.delta,mul_one,hn,add_sub_cancel] using hq.2
      · intro e _ _; exact hw e
    · have hn : (((-(q.2-p.2)).toNat : ℕ) : ℤ)=p.2-q.2 := by omega
      rw [show ds=List.replicate (-(q.2-p.2)).toNat Step.south by simp [ds,vertical,hle],
        hp',pathCost_replicate_edgeSet]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply vertical_straight_subset X lo hi p.2 .south _ (Or.inr rfl) hp.2
        simpa [Step.delta,neg_sub,Int.toNat_of_nonneg (show 0 ≤ p.2-q.2 by omega)] using hq.2
      · intro e _ _; exact hw e
  · rw [hp']
    by_cases hle : p.2 ≤ q.2
    · have hn : (((q.2-p.2).toNat : ℕ) : ℤ)=q.2-p.2 := Int.toNat_of_nonneg (by omega)
      rw [show ds=List.replicate (q.2-p.2).toNat Step.north by simp [ds,vertical,hle]]
      apply vertical_straight_in X lo hi p.2 .north _ (Or.inl rfl) hp.2
      simpa only [Step.delta,mul_one,hn,add_sub_cancel] using hq.2
    · have hn : (((-(q.2-p.2)).toNat : ℕ) : ℤ)=p.2-q.2 := by omega
      rw [show ds=List.replicate (-(q.2-p.2)).toNat Step.south by simp [ds,vertical,hle]]
      apply vertical_straight_in X lo hi p.2 .south _ (Or.inr rfl) hp.2
      simpa [Step.delta,neg_sub,Int.toNat_of_nonneg (show 0 ≤ p.2-q.2 by omega)] using hq.2

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnectionGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma transverse_interval_all_pairs (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b : ℝ) (X : ℤ) (lo hi : ℝ) (p q : Vertex)
    (hp : p.1=X ∧ lo ≤ transverse b p ∧ transverse b p ≤ hi)
    (hq : q.1=X ∧ lo ≤ transverse b q ∧ transverse b q ≤ hi) :
    ∃ ds, p+displacement ds=q ∧
      pathCost w p ds ≤ ∑ e ∈ transverseIntervalEdges b X lo hi,w e ∧
      PathIn p ds {z | z.1=X ∧ lo ≤ transverse b z ∧ transverse b z ≤ hi} := by
  have conv (z : Vertex) (hz : z.1=X) :
      (lo ≤ transverse b z ∧ transverse b z ≤ hi) ↔
      (⌈lo+b*X⌉ ≤ z.2 ∧ z.2 ≤ ⌊hi+b*X⌋) := by
    rw [Int.ceil_le,Int.le_floor]
    simp only [transverse,hz]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  obtain ⟨ds,hd,hc,hin⟩ := vertical_interval_all_pairs w hw X ⌈lo+b*X⌉ ⌊hi+b*X⌋ p q
    ⟨hp.1,(conv p hp.1).mp hp.2⟩ ⟨hq.1,(conv q hq.1).mp hq.2⟩
  refine ⟨ds,hd,hc,?_⟩
  intro i hi'
  have hz := hin i hi'
  exact ⟨hz.1,(conv _ hz.1).mpr hz.2⟩

lemma grid_bin_endpoint (j : ℕ) (hj : 1 ≤ j) (h w : ℤ) (hw : 1 ≤ w)
    (r₀ r : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (hr : |r-r₀| ≤ 1) : gridIntervalLower h w ≤ r ∧ r ≤ gridIntervalUpper j h w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hprod : 0 ≤ (30*(j : ℝ)^2+8)*(w : ℝ) := by positivity
  have hh := abs_le.mp hr
  unfold gridIntervalLower gridIntervalUpper
  constructor <;> nlinarith [hbin.1,hbin.2,hh.1,hh.2]

lemma grid_trial_vertex_interval (b : ℝ) (X h w l : ℤ) (j : ℕ) (hw : 1 ≤ w)
    (t : Fin (j^2)) (p : Vertex)
    (hp : p ∈ rareFastRegion b 1 8 w l (gridTrialTranslate b X h w t)) :
    gridIntervalLower h w ≤ transverse b p ∧ transverse b p ≤ gridIntervalUpper j h w := by
  have hf := Int.floor_le (b*X)
  have hf' := Int.lt_floor_add_one (b*X)
  have ht : (t : ℝ)+1 ≤ (j : ℝ)^2 := by exact_mod_cast t.isLt
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hr : |transverse b p-transverse b (gridTrialTranslate b X h w t)| ≤ 8*w := by
    convert hp.2.2 using 1
    simp [transverse]
    congr 1
    ring
  rw [gridTrialTranslate_center] at hr
  have hh := abs_le.mp hr
  have htu := mul_le_mul_of_nonneg_right ht (show 0 ≤ 30*(w : ℝ) by positivity)
  have htl := mul_nonneg ht0 (show 0 ≤ 30*(w : ℝ) by positivity)
  unfold gridIntervalLower gridIntervalUpper
  constructor <;> nlinarith [hh.1,hh.2]

lemma grid_interval_localization (j : ℕ) (hj : 1 ≤ j) (h w : ℤ) (hw : 1 ≤ w)
    (r₀ r : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (hr : gridIntervalLower h w ≤ r ∧ r ≤ gridIntervalUpper j h w) :
    |r-r₀| ≤ 50*(j : ℝ)^2*w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ (w : ℝ) by linarith)
  unfold gridIntervalLower gridIntervalUpper at hr
  apply abs_le.mpr
  constructor <;> nlinarith [hbin.1,hbin.2,hr.1,hr.2]

theorem grid_bin_connection (weights : Edge → ℝ) (hweights : ∀ e, 0 ≤ weights e)
    (b m K : ℝ) (hK : 0 ≤ K) (X h w l : ℤ) (hl : 0 ≤ l) (j : ℕ)
    (hj : 1 ≤ j) (hw : 1 ≤ w)
    (htrial : ∃ t : Fin (j^2), weights ∈ crossingEvent b m K w l (gridTrialTranslate b X h w t))
    (hleft : (∑ e ∈ transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w),
      weights e) ≤ 100*(j : ℝ)^2*w)
    (hright : (∑ e ∈ transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w),
      weights e) ≤ 100*(j : ℝ)^2*w)
    (r₀ : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (p q : Vertex) (hp : p.1=X ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=X+l ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧ pathCost weights p ds ≤ m*l+(K+200)*(j : ℝ)^2*w ∧
      PathIn p ds {z | X-l ≤ z.1 ∧ z.1 ≤ X+2*l ∧
        |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*w} := by
  obtain ⟨t,a,ds,hcols,hin,hcost⟩ := htrial
  have ha : a.1=X := hcols.1
  have hz : (a+displacement ds).1=X+l := hcols.2
  have hpath : PathIn a ds (rareFastRegion b 1 8 w l (gridTrialTranslate b X h w t)) := by
    intro i hi
    exact (mem_rareFastVertices ..).mp (hin i hi)
  have hai := grid_trial_vertex_interval b X h w l j hw t a (by simpa using hpath 0 (by omega))
  have hzi := grid_trial_vertex_interval b X h w l j hw t (a+displacement ds)
    (pathIn_endpoint _ _ _ hpath)
  obtain ⟨left,hld,hlcost,hlin⟩ := transverse_interval_all_pairs weights hweights b X
    (gridIntervalLower h w) (gridIntervalUpper j h w) p a
    ⟨hp.1,grid_bin_endpoint j hj h w hw r₀ _ hbin hp.2⟩ ⟨ha,hai⟩
  obtain ⟨right,hrd,hrcost,hrin⟩ := transverse_interval_all_pairs weights hweights b (X+l)
    (gridIntervalLower h w) (gridIntervalUpper j h w) (a+displacement ds) q
    ⟨hz,hzi⟩ ⟨hq.1,grid_bin_endpoint j hj h w hw r₀ _ hbin hq.2⟩
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ K*(w : ℝ) by positivity)
  have hbound : 50*(j : ℝ)^2*w ≤ (K+200)*(j : ℝ)^2*w := by
    nlinarith [mul_nonneg hK (show 0 ≤ (j : ℝ)^2*(w : ℝ) by positivity)]
  let S : Set Vertex := {z | X-l ≤ z.1 ∧ z.1 ≤ X+2*l ∧
    |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*w}
  have hlin' : PathIn p left S := by
    intro i hi
    have hh := hlin i hi
    have hx : (p+displacement (left.take i)).1=X := hh.1
    exact ⟨by omega,by omega,(grid_interval_localization j hj h w hw r₀ _ hbin hh.2).trans hbound⟩
  have hrin' : PathIn (a+displacement ds) right S := by
    intro i hi
    have hh := hrin i hi
    have hx : (a+displacement ds+displacement (right.take i)).1=X+l := hh.1
    exact ⟨by omega,by omega,(grid_interval_localization j hj h w hw r₀ _ hbin hh.2).trans hbound⟩
  have hin' : PathIn a ds S := by
    intro i hi
    have hh := hpath i hi
    have hix := hh.1
    have hix' := hh.2.1
    have hlo : X-l ≤ (a+displacement (ds.take i)).1 := by
      simp only [gridTrialTranslate,Prod.fst_sub,Int.cast_sub] at hix
      exact_mod_cast (show (X : ℝ)-l ≤ ((a+displacement (ds.take i)).1 : ℝ) by linarith)
    have hhi : (a+displacement (ds.take i)).1 ≤ X+2*l := by
      simp only [gridTrialTranslate,Prod.fst_sub,Int.cast_sub] at hix'
      exact_mod_cast (show ((a+displacement (ds.take i)).1 : ℝ) ≤ (X : ℝ)+2*l by linarith)
    exact ⟨hlo,hhi,(grid_interval_localization j hj h w hw r₀ _ hbin
      (grid_trial_vertex_interval b X h w l j hw t _ hh)).trans hbound⟩
  refine ⟨left++ds++right,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc,hld,hrd]
  · rw [pathCost_append,pathCost_append,hld,displacement_append,← add_assoc,hld]
    linarith
  · apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hlin' (by simpa [hld] using hin'))
    simpa [displacement_append,← add_assoc,hld] using hrin'

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

lemma gridBinGood_connection (weights : Edge → ℝ) (hweights : ∀ e, 0 ≤ weights e)
    (b m K : ℝ) (hK : 0 ≤ K) (X h w l : ℤ) (hl : 0 ≤ l) (j : ℕ)
    (hj : 1 ≤ j) (hw : 1 ≤ w) (hgood : weights ∈ gridBinGood b m K X h w l j)
    (r₀ : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (p q : Vertex) (hp : p.1=X ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=X+l ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧ pathCost weights p ds ≤ m*l+(K+200)*(j : ℝ)^2*w ∧
      PathIn p ds {z | X-l ≤ z.1 ∧ z.1 ≤ X+2*l ∧
        |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*w} :=
  grid_bin_connection weights hweights b m K hK X h w l hl j hj hw
    hgood.1 hgood.2.1 hgood.2.2 r₀ hbin p q hp hq

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridTail
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Finset Set
open scoped Topology

lemma gridFailureTail_tendsto (C q : ℝ) (_hq : 0 < q) :
    Tendsto (gridFailureTail C q) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (gridFailureSeries q)
  change Tendsto (fun J : ℕ => C*(∑' n : ℕ,gridFailureSeries q (n+J))) atTop (𝓝 0)
  simpa only [mul_zero] using h.const_mul C

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnections
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem gridConnectionsEvent_paths (weights : Edge → ℝ)
    (b m₀ K A R : ℝ) (hK : 0 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : weights ∈ gridConnectionsEvent b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m) (i : ℤ)
    (hi : -(A+4)*(2 : ℝ)^m ≤ ((gridMesh m j*i : ℤ) : ℝ) ∧
      ((gridMesh m j*i+gridMesh m j : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r₀ : ℝ) (hr : |r₀| ≤ R*(2 : ℝ)^k)
    (p q : Vertex)
    (hp : p.1=gridMesh m j*i ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=gridMesh m j*i+gridMesh m j ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧
      pathCost weights p ds ≤ m₀*(gridMesh m j)+(K+200)*(j : ℝ)^2*(gridWidth k j) ∧
      PathIn p ds {z | gridMesh m j*i-gridMesh m j ≤ z.1 ∧
        z.1 ≤ gridMesh m j*i+2*gridMesh m j ∧
        |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*(gridWidth k j)} := by
  have hn : j-J ∈ Finset.range (gridLastLevel m+1-J) := by rw [Finset.mem_range]; omega
  have he : j-J+J=j := by omega
  have htest := hg.2 (j-J) hn
  rw [he] at htest
  have hpos := gridMesh_pos m j
  have hpos' : (0 : ℝ) < gridMesh m j := by exact_mod_cast hpos
  have hi' : -(A+4)*(2 : ℝ)^m ≤ ((gridMesh m j*i : ℤ) : ℝ) ∧
      ((gridMesh m j*i : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m := by
    refine ⟨hi.1,?_⟩
    have hh := hi.2
    push_cast at hh ⊢
    linarith
  have hm := grid_interval_index_mem A R ((2 : ℝ)^m) ((2 : ℝ)^k)
    (gridMesh m j) (gridWidth k j) hpos (gridWidth_pos k j) i r₀ hi' hr
  exact gridBinGood_connection weights hg.1 b m₀ K hK _ _ _ _ hpos.le j
    (by omega) (gridWidth_pos k j) (htest _ hm) r₀
    (grid_bin_floor (gridWidth k j) (gridWidth_pos k j) r₀) p q hp hq

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointBlocks
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem gridConnections_block (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m)
    (he : (K+200)*(j : ℝ)^2*(gridWidth k j) ≤ H)
    (X : ℤ) (hX : gridMesh m j ∣ X) (n : ℕ)
    (hlo : -(A+4)*(2 : ℝ)^m ≤ (X : ℝ))
    (hhi : ((X+(n : ℤ)*gridMesh m j : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) :
    ∃ ds, endpointVertex b r X+displacement ds=
        endpointVertex b r (X+(n : ℤ)*gridMesh m j) ∧
      pathCost w (endpointVertex b r X) ds ≤
        m₀*((n : ℤ)*gridMesh m j : ℤ)+(n : ℝ)*((K+200)*(j : ℝ)^2*gridWidth k j) ∧
      PathIn (endpointVertex b r X) ds {z | X-gridMesh m j ≤ z.1 ∧
        z.1 ≤ X+(n : ℤ)*gridMesh m j+gridMesh m j ∧ |transverse b z-r| ≤ H} := by
  let d := gridMesh m j
  let p (i : ℕ) := endpointVertex b r (X+(i : ℤ)*d)
  let S : Set Vertex := {z | X-d ≤ z.1 ∧ z.1 ≤ X+(n : ℤ)*d+d ∧ |transverse b z-r| ≤ H}
  let c : ℝ := m₀*d+(K+200)*(j : ℝ)^2*gridWidth k j
  have hd : 0 < d := gridMesh_pos m j
  have hp0 : p 0 ∈ S := by
    dsimp [p,S,endpointVertex]
    refine ⟨by omega,?_,?_⟩
    · have hn : (0 : ℤ) ≤ n := by positivity
      nlinarith
    · simpa [endpointVertex] using (endpointVertex_close b r X).le.trans hH
  have step (i : ℕ) (hi : i < n) :
      ∃ ds, p i+displacement ds=p (i+1) ∧ pathCost w (p i) ds ≤ c ∧ PathIn (p i) ds S := by
    have hdiv : d ∣ X+(i : ℤ)*d := dvd_add hX (dvd_mul_left _ _)
    obtain ⟨q,hq⟩ := hdiv
    have hq' : gridMesh m j*q=X+(i : ℤ)*d := hq.symm
    have hicol : (X : ℝ) ≤ ((X+(i : ℤ)*d : ℤ) : ℝ) := by
      exact_mod_cast (show X ≤ X+(i : ℤ)*d by have h : 0 ≤ (i : ℤ)*d := mul_nonneg (by positivity) hd.le; omega)
    have hiend : X+(i : ℤ)*d+d ≤ X+(n : ℤ)*d := by
      have hi' : (i : ℤ)+1 ≤ n := by omega
      nlinarith
    have hir : ((X+(i : ℤ)*d+d : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m := by
      exact (by exact_mod_cast hiend : ((X+(i : ℤ)*d+d : ℤ) : ℝ) ≤ ((X+(n : ℤ)*d : ℤ) : ℝ)).trans hhi
    obtain ⟨ds,hend,hcost,hin⟩ := gridConnectionsEvent_paths w b m₀ K A R hK k m J hJ hg j hj q
      ⟨by simpa [hq'] using hlo.trans hicol,by simpa [hq'] using hir⟩ r hr (p i) (p (i+1))
      ⟨by simpa [p,endpointVertex] using hq'.symm,(endpointVertex_close b r _).le⟩
      ⟨by simp [p,endpointVertex,hq',Nat.cast_add,Nat.cast_one]; ring,(endpointVertex_close b r _).le⟩
    refine ⟨ds,hend,hcost,?_⟩
    intro t ht
    have hz := hin t ht
    rw [hq'] at hz
    change X+(i : ℤ)*d-d ≤ (p i+displacement (ds.take t)).1 ∧
      (p i+displacement (ds.take t)).1 ≤ X+(i : ℤ)*d+2*d ∧
      |transverse b (p i+displacement (ds.take t))-r| ≤ (K+200)*(j : ℝ)^2*gridWidth k j at hz
    change X-d ≤ (p i+displacement (ds.take t)).1 ∧
      (p i+displacement (ds.take t)).1 ≤ X+(n : ℤ)*d+d ∧ _
    refine ⟨?_,?_,hz.2.2.trans he⟩
    · have hi0 : (0 : ℤ) ≤ i := by positivity
      nlinarith [hz.1]
    · nlinarith [hz.2.1]
  obtain ⟨ds,hend,hcost,hin⟩ := exists_path_chain w p S (fun _ => c) n hp0 step
  refine ⟨ds,by simpa [p] using hend,?_,by simpa [p,S] using hin⟩
  have heq : (∑ _i ∈ range n,c) =
      m₀*((n : ℤ)*gridMesh m j : ℤ)+(n : ℝ)*((K+200)*(j : ℝ)^2*gridWidth k j) := by
    simp [c,d]
    ring
  rw [heq] at hcost
  simpa [p] using hcost

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointConnection
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma ColumnConnection.mono {w : Edge → ℝ} {b r m₀ E F : ℝ} {S T : Set Vertex} {X Y : ℤ}
    (h : ColumnConnection w b r m₀ E S X Y) (hE : E ≤ F) (hS : S ⊆ T) :
    ColumnConnection w b r m₀ F T X Y := by
  obtain ⟨ds,hd,hc,hin⟩ := h
  exact ⟨ds,hd,by linarith,fun i hi => hS (hin i hi)⟩

lemma ColumnConnection.trans {w : Edge → ℝ} {b r m₀ E F : ℝ} {S : Set Vertex} {X Y Z : ℤ}
    (h : ColumnConnection w b r m₀ E S X Y) (g : ColumnConnection w b r m₀ F S Y Z) :
    ColumnConnection w b r m₀ (E+F) S X Z := by
  obtain ⟨ds,hd,hc,hin⟩ := h
  obtain ⟨es,he,hce,hine⟩ := g
  refine ⟨ds++es,?_,?_,?_⟩
  · rw [displacement_append,← add_assoc,hd,he]
  · rw [pathCost_append,hd]
    push_cast at hc hce ⊢
    linarith
  · exact pathIn_append _ _ _ _ hin (by simpa [hd] using hine)

lemma gridConnections_block_connection (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m)
    (he : (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (X Y B T : ℤ) (hX : gridMesh m j ∣ X) (n : ℕ) (hn : n ≤ 16)
    (hXY : X+(n : ℤ)*gridMesh m j=Y)
    (hlo : -(A+4)*(2 : ℝ)^m ≤ (X : ℝ))
    (hhi : (Y : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (hB : B ≤ X-gridMesh m j) (hT : Y+gridMesh m j ≤ T)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) :
    ColumnConnection w b r m₀ (16*((K+200)*(j : ℝ)^2*gridWidth k j))
      (endpointTube b r H B T) X Y := by
  obtain ⟨ds,hd,hc,hin⟩ := gridConnections_block w b m₀ K A R H hK hH k m J hJ hg j hj he
    X hX n hlo (by simpa [hXY] using hhi) r hr
  have hn' : (n : ℝ) ≤ 16 := by exact_mod_cast hn
  have herr : (n : ℝ)*((K+200)*(j : ℝ)^2*gridWidth k j) ≤
      16*((K+200)*(j : ℝ)^2*gridWidth k j) := by
    apply mul_le_mul_of_nonneg_right hn'
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by exact_mod_cast (gridWidth_pos k j).le)
  refine ⟨ds,by simpa [hXY] using hd,?_,?_⟩
  · have heq : (n : ℤ)*gridMesh m j=Y-X := by omega
    rw [heq] at hc
    linarith
  · intro i hi
    have hz := hin i hi
    rw [hXY] at hz
    exact ⟨hB.trans hz.1,hz.2.1.trans hT,hz.2.2⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointEntrance
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem gridConnections_entrance_levels (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (x : ℤ) (hlo : -(A+4)*(2 : ℝ)^m ≤ (entranceColumn x m J : ℝ))
    (hhi : (x : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) (n : ℕ) (hn : J+n ≤ gridLastLevel m) :
    ColumnConnection w b r m₀
      (∑ i ∈ range (n+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
      (endpointTube b r H (entranceColumn x m J-gridMesh m J) (x+gridMesh m J))
      (entranceColumn x m J) (endpointColumn x m (J+n)) := by
  let B := entranceColumn x m J
  let d := gridMesh m J
  have hfloor (j : ℕ) : endpointColumn x m j ≤ x :=
    (meshFloor_bounds x _ (gridMesh_pos m j)).1
  have hfloorR (j : ℕ) : (endpointColumn x m j : ℝ) ≤ (x : ℝ) := by exact_mod_cast hfloor j
  have hB (j : ℕ) (hj : J ≤ j) : B ≤ endpointColumn x m j := by
    have hm := endpointColumn_mono x m hj
    have hd := gridMesh_pos m J
    dsimp [B,entranceColumn]
    omega
  induction n with
  | zero =>
    have hb := gridConnections_block_connection w b m₀ K A R H hK hH k m J hJ hg J
      ⟨le_refl _,by simpa using hn⟩ (herr J le_rfl (by simpa using hn)) B
      (endpointColumn x m J) (B-d) (x+d) (entranceColumn_dvd x m J) 1 (by omega)
      (by simp [B,entranceColumn]) hlo
      ((hfloorR J).trans hhi) (by rfl) (by dsimp [d]; have hh := hfloor J; omega) r hr
    simpa [B,d] using hb
  | succ n ih =>
    have hn' : J+n ≤ gridLastLevel m := by omega
    have hj : J ≤ J+n+1 := by omega
    have hjlast : J+n+1 ≤ gridLastLevel m := by omega
    have hp := ih hn'
    obtain ⟨N,hN,hstep⟩ := endpointColumn_step x m (J+n)
    have hdiv : gridMesh m (J+n+1) ∣ endpointColumn x m (J+n) :=
      dvd_trans (gridMesh_divides m (J+n)) (meshFloor_dvd x _)
    have hdm : gridMesh m (J+n+1) ≤ d := gridMesh_antitone m hj
    have hbefore := hB (J+n) (by omega)
    have hb := gridConnections_block_connection w b m₀ K A R H hK hH k m J hJ hg (J+n+1)
      ⟨hj,hjlast⟩ (herr _ hj hjlast) (endpointColumn x m (J+n))
      (endpointColumn x m (J+n+1)) (B-d) (x+d) hdiv N (by omega) hstep
      (hlo.trans (by exact_mod_cast hbefore))
      ((hfloorR (J+n+1)).trans hhi)
      (by omega) (by have hh := hfloor (J+n+1); omega) r hr
    have hc := hp.trans hb
    simpa only [sum_range_succ,Nat.add_assoc] using hc

theorem gridConnections_entrance (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J) (hlast : J ≤ gridLastLevel m)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (p : Vertex) (hlo : -(A+4)*(2 : ℝ)^m ≤ (entranceColumn p.1 m J : ℝ))
    (hhi : (p.1 : ℝ) ≤ (A+4)*(2 : ℝ)^m) (hr : |transverse b p| ≤ R*(2 : ℝ)^k) :
    ∃ ds, endpointVertex b (transverse b p) (entranceColumn p.1 m J)+displacement ds=p ∧
      pathCost w (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds ≤
        m₀*((p.1-entranceColumn p.1 m J : ℤ) : ℝ)+
        ∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)) ∧
      PathIn (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds
        (endpointTube b (transverse b p) H (entranceColumn p.1 m J-gridMesh m J) (p.1+gridMesh m J)) := by
  have hc := gridConnections_entrance_levels w b m₀ K A R H hK hH k m J hJ hg herr
    p.1 hlo hhi (transverse b p) hr (gridLastLevel m-J) (by omega)
  rw [Nat.add_sub_of_le hlast,endpointColumn_last] at hc
  simpa only [ColumnConnection,endpointVertex_self] using hc

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointExit
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem gridConnections_exit_levels (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (x : ℤ) (hlo : -(A+4)*(2 : ℝ)^m ≤ (x : ℝ))
    (hhi : (exitColumn x m J : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) (n : ℕ) (hn : J+n ≤ gridLastLevel m) :
    ColumnConnection w b r m₀
      (∑ i ∈ range (n+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
      (endpointTube b r H (x-gridMesh m J) (exitColumn x m J+gridMesh m J))
      (-endpointColumn (-x) m (J+n)) (exitColumn x m J) := by
  let T := exitColumn x m J
  let d := gridMesh m J
  have hfloor (j : ℕ) : x ≤ -endpointColumn (-x) m j := by
    have h := (meshFloor_bounds (-x) (gridMesh m j) (gridMesh_pos m j)).1
    change meshFloor (-x) (gridMesh m j) ≤ -x at h
    dsimp [endpointColumn]
    omega
  have hT (j : ℕ) (hj : J ≤ j) : -endpointColumn (-x) m j ≤ T := by
    have hm := endpointColumn_mono (-x) m hj
    have hd := gridMesh_pos m J
    dsimp [T,exitColumn,entranceColumn]
    omega
  induction n with
  | zero =>
    have hdiv : gridMesh m J ∣ -endpointColumn (-x) m J := dvd_neg.mpr (meshFloor_dvd (-x) _)
    have hb := gridConnections_block_connection w b m₀ K A R H hK hH k m J hJ hg J
      ⟨le_refl _,by simpa using hn⟩ (herr J le_rfl (by simpa using hn))
      (-endpointColumn (-x) m J) T (x-d) (T+d) hdiv 1 (by omega)
      (by simp [T,exitColumn,entranceColumn]; ring)
      (hlo.trans (by exact_mod_cast hfloor J)) hhi
      (by dsimp [d]; have hh := hfloor J; omega) (by rfl) r hr
    simpa [T,d] using hb
  | succ n ih =>
    have hn' : J+n ≤ gridLastLevel m := by omega
    have hj : J ≤ J+n+1 := by omega
    have hjlast : J+n+1 ≤ gridLastLevel m := by omega
    have hp := ih hn'
    obtain ⟨N,hN,hstep⟩ := endpointColumn_step (-x) m (J+n)
    have hdiv : gridMesh m (J+n+1) ∣ -endpointColumn (-x) m (J+n+1) :=
      dvd_neg.mpr (meshFloor_dvd (-x) _)
    have hdm : gridMesh m (J+n+1) ≤ d := gridMesh_antitone m hj
    have hbefore := hT (J+n) (by omega)
    have hstart := hfloor (J+n+1)
    have hb := gridConnections_block_connection w b m₀ K A R H hK hH k m J hJ hg (J+n+1)
      ⟨hj,hjlast⟩ (herr _ hj hjlast) (-endpointColumn (-x) m (J+n+1))
      (-endpointColumn (-x) m (J+n)) (x-d) (T+d) hdiv N (by omega) (by omega)
      (hlo.trans (by exact_mod_cast hstart))
      ((by exact_mod_cast hbefore : ((-endpointColumn (-x) m (J+n) : ℤ) : ℝ) ≤ (T : ℝ)).trans hhi) (by omega) (by omega) r hr
    have hc := hb.trans hp
    rw [add_comm (16*((K+200)*((J+n+1 : ℕ) : ℝ)^2*gridWidth k (J+n+1)))] at hc
    simpa only [sum_range_succ,Nat.add_assoc] using hc

theorem gridConnections_exit (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J) (hlast : J ≤ gridLastLevel m)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (p : Vertex) (hlo : -(A+4)*(2 : ℝ)^m ≤ (p.1 : ℝ))
    (hhi : (exitColumn p.1 m J : ℝ) ≤ (A+4)*(2 : ℝ)^m) (hr : |transverse b p| ≤ R*(2 : ℝ)^k) :
    ∃ ds, p+displacement ds=endpointVertex b (transverse b p) (exitColumn p.1 m J) ∧
      pathCost w p ds ≤ m₀*((exitColumn p.1 m J-p.1 : ℤ) : ℝ)+
        ∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)) ∧
      PathIn p ds (endpointTube b (transverse b p) H (p.1-gridMesh m J) (exitColumn p.1 m J+gridMesh m J)) := by
  have hc := gridConnections_exit_levels w b m₀ K A R H hK hH k m J hJ hg herr
    p.1 hlo hhi (transverse b p) hr (gridLastLevel m-J) (by omega)
  rw [Nat.add_sub_of_le hlast,endpointColumn_last,neg_neg] at hc
  simpa only [ColumnConnection,endpointVertex_self] using hc

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointExtensions
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem gridConnections_endpoint_extensions (w : Edge → ℝ) (b m₀ K A R : ℝ)
    (hK : 0 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m)
    (hlast : gridLastLevel m ≤ k)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (p : Vertex) (hp : p ∈ endpointBox b A R k m) :
    ColumnConnection w b (transverse b p) m₀ (endpointExtensionError K k J)
      (endpointBox b (A+4) (R+2*(K+200)) k m) (entranceColumn p.1 m J) p.1 ∧
    ColumnConnection w b (transverse b p) m₀ (endpointExtensionError K k J)
      (endpointBox b (A+4) (R+2*(K+200)) k m) p.1 (exitColumn p.1 m J) := by
  let H := 2*(K+200)*(2 : ℝ)^k
  have hH : 1 ≤ H := by
    have hs := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
    dsimp [H]
    nlinarith
  have herr (j : ℕ) (_hj : J ≤ j) (hjl : j ≤ gridLastLevel m) :
      (K+200)*(j : ℝ)^2*gridWidth k j ≤ H := grid_endpoint_height K hK k j (hjl.trans hlast)
  have hd := gridMesh_pos m J
  have hdR : (0 : ℝ) < gridMesh m J := by exact_mod_cast hd
  have hmesh := gridMesh_le_scale m J
  have hL : (0 : ℝ) < 2^m := by positivity
  have hs := entranceColumn_span p.1 m J
  have ht := exitColumn_span p.1 m J
  have hsR : (gridMesh m J : ℝ) ≤ (p.1 : ℝ)-(entranceColumn p.1 m J : ℝ) ∧
      (p.1 : ℝ)-(entranceColumn p.1 m J : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast hs
  have htR : (gridMesh m J : ℝ) ≤ (exitColumn p.1 m J : ℝ)-(p.1 : ℝ) ∧
      (exitColumn p.1 m J : ℝ)-(p.1 : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast ht
  have hpx := abs_le.mp hp.1
  have hleft : -(A+4)*(2 : ℝ)^m ≤ (entranceColumn p.1 m J : ℝ) := by linarith [hsR.2]
  have hright : (exitColumn p.1 m J : ℝ) ≤ (A+4)*(2 : ℝ)^m := by linarith [htR.2]
  have hpL : -(A+4)*(2 : ℝ)^m ≤ (p.1 : ℝ) := by linarith [hpx.1]
  have hpR : (p.1 : ℝ) ≤ (A+4)*(2 : ℝ)^m := by linarith [hpx.2]
  have hentr := gridConnections_entrance w b m₀ K A R H hK hH k m J hJ hJlast hg herr p hleft hpR hp.2
  have hexit := gridConnections_exit w b m₀ K A R H hK hH k m J hJ hJlast hg herr p hpL hright hp.2
  have hc := endpoint_extension_cost_sum K hK k m J hlast hJlast
  constructor
  · have hconn : ColumnConnection w b (transverse b p) m₀
        (∑ i ∈ Finset.range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
        (endpointTube b (transverse b p) H (entranceColumn p.1 m J-gridMesh m J) (p.1+gridMesh m J))
        (entranceColumn p.1 m J) p.1 := by
      simpa only [ColumnConnection,endpointVertex_self] using hentr
    apply hconn.mono hc
    intro z hz
    apply endpoint_localization b A R (K+200) (by linarith) k m p z (gridMesh m J) hmesh hp.1 hp.2
    · exact ⟨by have hh := hz.1; omega,
        by have hh := hz.2.1; omega⟩
    · exact hz.2.2
  · have hconn : ColumnConnection w b (transverse b p) m₀
        (∑ i ∈ Finset.range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
        (endpointTube b (transverse b p) H (p.1-gridMesh m J) (exitColumn p.1 m J+gridMesh m J))
        p.1 (exitColumn p.1 m J) := by
      simpa only [ColumnConnection,endpointVertex_self] using hexit
    apply hconn.mono hc
    intro z hz
    apply endpoint_localization b A R (K+200) (by linarith) k m p z (gridMesh m J) hmesh hp.1 hp.2
    · exact ⟨by have hh := hz.1; omega,
        by have hh := hz.2.1; omega⟩
    · exact hz.2.2

theorem gridConnections_endpoint_defects (w : Edge → ℝ) (b m₀ K A R : ℝ)
    (hK : 0 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m)
    (hlast : gridLastLevel m ≤ k)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (p : Vertex) (hp : p ∈ endpointBox b A R k m) :
    ∃ ds es,
      endpointVertex b (transverse b p) (entranceColumn p.1 m J)+displacement ds=p ∧
      p+displacement es=endpointVertex b (transverse b p) (exitColumn p.1 m J) ∧
      (∀ a : ℝ, defect w b m₀ a (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds ≤
        endpointExtensionError K k J+|a|) ∧
      (∀ a : ℝ, defect w b m₀ a p es ≤ endpointExtensionError K k J+|a|) ∧
      PathIn (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds
        (endpointBox b (A+4) (R+2*(K+200)) k m) ∧
      PathIn p es (endpointBox b (A+4) (R+2*(K+200)) k m) := by
  obtain ⟨⟨ds,hd,hc,hin⟩,⟨es,he,hce,hine⟩⟩ :=
    gridConnections_endpoint_extensions w b m₀ K A R hK k m J hJ hJlast hlast hg p hp
  refine ⟨ds,es,by simpa only [endpointVertex_self] using hd,
    by simpa only [endpointVertex_self] using he,?_,?_,hin,by simpa only [endpointVertex_self] using hine⟩
  · intro a
    exact endpoint_path_defect w b (transverse b p) m₀ a _ _ _ ds hd hc
  · intro a
    simpa only [endpointVertex_self] using endpoint_path_defect w b (transverse b p) m₀ a _ _ _ es he hce

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointCoarse
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma endpoint_coarse_columns (A : ℝ) (m J : ℕ) (x : ℤ)
    (hx : |(x : ℝ)| ≤ A*(2 : ℝ)^m) :
    |(entranceColumn x m J : ℝ)| ≤ (A+2)*(2 : ℝ)^m ∧
      |(exitColumn x m J : ℝ)| ≤ (A+2)*(2 : ℝ)^m := by
  have hl := entranceColumn_span x m J
  have hr := exitColumn_span x m J
  have hl' : (gridMesh m J : ℝ) ≤ (x : ℝ)-(entranceColumn x m J : ℝ) ∧
      (x : ℝ)-(entranceColumn x m J : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast hl
  have hr' : (gridMesh m J : ℝ) ≤ (exitColumn x m J : ℝ)-(x : ℝ) ∧
      (exitColumn x m J : ℝ)-(x : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast hr
  have hd := gridMesh_le_scale m J
  have hd0 : (0 : ℝ) < gridMesh m J := by exact_mod_cast gridMesh_pos m J
  have hx' := abs_le.mp hx
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hl'.1,hl'.2,hr'.1,hr'.2]

lemma endpointBox_mono (b A A' R R' : ℝ) (k m : ℕ) (hA : A ≤ A') (hR : R ≤ R') :
    endpointBox b A R k m ⊆ endpointBox b A' R' k m := by
  intro p hp
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_right hA (by positivity)),
    hp.2.trans (mul_le_mul_of_nonneg_right hR (by positivity))⟩

theorem gridConnections_extend_negative_path (w : Edge → ℝ) (b m₀ K A R a ε : ℝ)
    (hK : 0 ≤ K) (hm : 0 < m₀) (hR : 0 ≤ R) (hε : 0 < ε)
    (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m) (hlast : gridLastLevel m ≤ k)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herror : 2*endpointExtensionError K k J+2*|a| ≤ ε*(2 : ℝ)^k/2)
    (hscale : (2*R*|a| /m₀)*(2 : ℝ)^k ≤ (gridMesh m J : ℝ))
    (p : Vertex) (ds : List Step) (hin : PathIn p ds (endpointBox b A R k m))
    (hcost : defect w b m₀ a p ds < -ε*(2 : ℝ)^k) :
    ∃ X Y : ℤ, gridMesh m J ∣ X ∧ gridMesh m J ∣ Y ∧
      |(X : ℝ)| ≤ (A+2)*(2 : ℝ)^m ∧ |(Y : ℝ)| ≤ (A+2)*(2 : ℝ)^m ∧
      (gridMesh m J : ℝ) ≤ ((Y-X : ℤ) : ℝ) ∧
      ∃ q es, q.1=X ∧ (q+displacement es).1=Y ∧
        PathIn q es (endpointBox b (A+4) (R+2*(K+200)) k m) ∧
        defect w b m₀ a q es < -(ε/2)*(2 : ℝ)^k := by
  let z := p+displacement ds
  have hp : p ∈ endpointBox b A R k m := by simpa using hin 0 (by omega)
  have hz : z ∈ endpointBox b A R k m := by simpa [z] using hin ds.length le_rfl
  obtain ⟨l,_unused,hl,_hu,hld,_hud,hil,_hiu⟩ :=
    gridConnections_endpoint_defects w b m₀ K A R hK k m J hJ hJlast hlast hg p hp
  obtain ⟨_unused',u,_hl,hu,_hld,hud,_hil,hiu⟩ :=
    gridConnections_endpoint_defects w b m₀ K A R hK k m J hJ hJlast hlast hg z hz
  let q := endpointVertex b (transverse b p) (entranceColumn p.1 m J)
  have hrev := negative_defect_reverse_span w hg.1 b m₀ a R ((2 : ℝ)^k) ε hm hR
    (by positivity) hε.le p z ds rfl hp.2 hz.2 hcost
  have hspan := extended_columns_span p.1 z.1 m J (2*R*|a| /m₀) ((2 : ℝ)^k)
    (by convert hrev using 1; ring) hscale
  refine ⟨entranceColumn p.1 m J,exitColumn z.1 m J,entranceColumn_dvd _ _ _,exitColumn_dvd _ _ _,
    (endpoint_coarse_columns A m J p.1 hp.1).1,(endpoint_coarse_columns A m J z.1 hz.1).2,
    hspan,q,l++ds++u,rfl,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc]
    change ((endpointVertex b (transverse b p) (entranceColumn p.1 m J)+displacement l+
      displacement ds)+displacement u).1=exitColumn z.1 m J
    rw [hl]
    change (z+displacement u).1=exitColumn z.1 m J
    rw [hu]
    rfl
  · have him : PathIn p ds (endpointBox b (A+4) (R+2*(K+200)) k m) := by
      intro i hi
      exact endpointBox_mono b A (A+4) R (R+2*(K+200)) k m (by linarith) (by linarith) (hin i hi)
    apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hil (by simpa [hl] using him))
    simpa only [displacement_append,← add_assoc,hl] using hiu
  · rw [defect_append,defect_append]
    have he : q+displacement l=p := hl
    have he' : q+displacement (l++ds)=z := by rw [displacement_append,← add_assoc,he]
    rw [he,he']
    have hb := hld a
    have hc := hud a
    change defect w b m₀ a q l ≤ _ at hb
    linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointCoarseGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

lemma gridMesh_scale_bound (m J : ℕ) :
    (2 : ℝ)^m ≤ (2 : ℝ)^(4*J+1)*(gridMesh m J : ℝ) :=
  (div_le_iff₀ (by exact_mod_cast gridMesh_pos m J)).mp (gridMesh_count_ratio m J)

lemma coarse_column_index (A : ℝ) (hA : 0 ≤ A) (m J : ℕ) (X : ℤ)
    (hX : gridMesh m J ∣ X) (hbound : |(X : ℝ)| ≤ (A+2)*(2 : ℝ)^m) :
    ∃ i ∈ coarseColumnIndices A J, X=gridMesh m J*i := by
  obtain ⟨i,hi⟩ := hX
  refine ⟨i,?_,hi⟩
  apply mem_gridIndexRange_of_abs_le
  have hd : (0 : ℝ) < gridMesh m J := by exact_mod_cast gridMesh_pos m J
  have hprod := mul_le_mul_of_nonneg_left (gridMesh_scale_bound m J) (by linarith : 0 ≤ A+2)
  rw [hi,Int.cast_mul,abs_mul,abs_of_pos hd] at hbound
  nlinarith

lemma endpointBox_into_rareFastRegion (b A R : ℝ) (hA : 0 ≤ A) (k m J : ℕ) (X Y : ℤ)
    (hX : |(X : ℝ)| ≤ (A+2)*(2 : ℝ)^m)
    (hspan : (gridMesh m J : ℝ) ≤ ((Y-X : ℤ) : ℝ)) :
    endpointBox b (A+4) R k m ⊆
      rareFastRegion b (coarseRegionFactor A J) (R+1) ((2 : ℝ)^k) (Y-X) (endpointVertex b 0 X) := by
  have hd : (0 : ℝ) < gridMesh m J := by exact_mod_cast gridMesh_pos m J
  have hY : (0 : ℝ) ≤ ((Y-X : ℤ) : ℝ) := hd.le.trans hspan
  have hscale : (2 : ℝ)^m ≤ (2 : ℝ)^(4*J+1)*((Y-X : ℤ) : ℝ) :=
    (gridMesh_scale_bound m J).trans (mul_le_mul_of_nonneg_left hspan (by positivity))
  intro z hz
  have hzabs : |(z.1 : ℝ)-(X : ℝ)| ≤ (2*A+6)*(2 : ℝ)^m :=
    (abs_sub _ _).trans (by linarith [hz.1])
  have habs : |(z.1 : ℝ)-(X : ℝ)| ≤ coarseRegionFactor A J*((Y-X : ℤ) : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ 2*A+8)
    unfold coarseRegionFactor
    have hp : (0 : ℝ) < 2^m := by positivity
    nlinarith
  have hcoord : ((z-endpointVertex b 0 X).1 : ℝ)=(z.1 : ℝ)-(X : ℝ) := by simp [endpointVertex]
  have htrans : transverse b (z-endpointVertex b 0 X)=transverse b z-transverse b (endpointVertex b 0 X) := by
    simp [transverse]; ring
  have ht : |transverse b (endpointVertex b 0 X)| ≤ 1 := by simpa using (endpointVertex_close b 0 X).le
  have hs : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  refine ⟨?_,?_,?_⟩
  · rw [hcoord]
    have hh := (abs_le.mp habs).1
    linarith
  · rw [hcoord]
    have hh := (abs_le.mp habs).2
    nlinarith
  · rw [htrans]
    exact (abs_sub _ _).trans (by linarith [hz.2])

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointAsymptotics
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

lemma endpoint_mesh_ratio_tendsto {ι : Type*} {l : Filter ι} (k m : ι → ℕ)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop) (J : ℕ) :
    Tendsto (fun i => (gridMesh (m i) J : ℝ)/(2 : ℝ)^(k i)) l atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [hratio.eventually (eventually_ge_atTop (B*(2 : ℝ)^(4*J+1)))] with i hi
  have hs : (0 : ℝ) < 2^(k i) := by positivity
  have hc : (0 : ℝ) < 2^(4*J+1) := by positivity
  have hh := (le_div_iff₀ hs).mp hi
  have hm := gridMesh_scale_bound (m i) J
  apply (le_div_iff₀ hs).mpr
  nlinarith

lemma endpoint_levels_eventually {ι : Type*} {l : Filter ι} (k m : ι → ℕ)
    (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
    (hm : ∀ᶠ i in l, m i ≤ 3*k i) (J : ℕ) :
    ∀ᶠ i in l, J ≤ gridLastLevel (m i) ∧ gridLastLevel (m i) ≤ k i := by
  filter_upwards [hratio.eventually (eventually_ge_atTop ((2 : ℝ)^(4*J+1))),
    hk.eventually (eventually_ge_atTop 2),hm] with i hi hki hmi
  have hs : (1 : ℝ) ≤ 2^(k i) := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ)^(4*J+1) ≤ (2 : ℝ)^(m i) := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^(k i))).mp hi
    have hc : (0 : ℝ) ≤ 2^(4*J+1) := by positivity
    nlinarith
  have hexp : 4*J+1 ≤ m i := by
    by_contra hh
    have hh' := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (show m i < 4*J+1 by omega)
    exact (not_lt_of_ge hpow) hh'
  unfold gridLastLevel
  omega

lemma endpoint_error_eventually {ι : Type*} {l : Filter ι} (k : ι → ℕ)
    (hk : Tendsto k l atTop) (K a ε : ℝ) (hε : 0 < ε) (J : ℕ)
    (hJ : 32*(K+200)*endpointErrorTail J ≤ ε/4) :
    ∀ᶠ i in l, 2*endpointExtensionError K (k i) J+2*|a| ≤ ε*(2 : ℝ)^(k i)/2 := by
  have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hk
  filter_upwards [hs.eventually (eventually_ge_atTop (8*|a| /ε))] with i hi
  have hh := (div_le_iff₀ hε).mp hi
  have hj := mul_le_mul_of_nonneg_right hJ (show 0 ≤ (2 : ℝ)^(k i) by positivity)
  simp only [Function.comp_apply] at hh
  unfold endpointExtensionError
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma mem_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (w : Edge → ℝ) :
    w ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔
      ∃ p ds, PathIn p ds (endpointBox b A R k m) ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  have hv : (endpointBoxVertices b A R k m : Set Vertex)=endpointBox b A R k m :=
    (endpointBox_finite b A R k m).coe_toFinset
  simp only [arbitraryEndpointEvent,strictLocalizedEvent,mem_ofPred_eq,true_and,hv,defect]
  constructor <;> rintro ⟨p,ds,hin,hc⟩ <;> exact ⟨p,ds,hin,by linarith⟩

theorem arbitraryEndpointEvent_coarse_cover (b m₀ K A R a ε : ℝ)
    (hK : 0 ≤ K) (hm : 0 < m₀) (hA : 0 ≤ A) (hR : 0 ≤ R) (hε : 0 < ε)
    (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m) (hlast : gridLastLevel m ≤ k)
    (herror : 2*endpointExtensionError K k J+2*|a| ≤ ε*(2 : ℝ)^k/2)
    (hscale : (2*R*|a| /m₀)*(2 : ℝ)^k ≤ (gridMesh m J : ℝ)) :
    arbitraryEndpointEvent b m₀ a A R ε k m ⊆
      (gridConnectionsEvent b m₀ K A R k m J)ᶜ ∪
        ⋃ ij ∈ coarsePairIndices A J,coarsePairEvent b m₀ a A (R+2*(K+200)) ε k m J ij := by
  intro w hw
  by_cases hg : w ∈ gridConnectionsEvent b m₀ K A R k m J
  · apply Or.inr
    obtain ⟨p,ds,hin,hcost⟩ := (mem_arbitraryEndpointEvent ..).mp hw
    obtain ⟨X,Y,hXd,hYd,hX,hY,hspan,q,es,hq,he,hpath,hdef⟩ :=
      gridConnections_extend_negative_path w b m₀ K A R a ε hK hm hR hε k m J hJ hJlast hlast hg
        herror hscale p ds hin hcost
    obtain ⟨i,hi,hXi⟩ := coarse_column_index A hA m J X hXd hX
    obtain ⟨j,hj,hYj⟩ := coarse_column_index A hA m J Y hYd hY
    have hij : i < j := by
      have hd := gridMesh_pos m J
      have hspan' : gridMesh m J ≤ Y-X := by exact_mod_cast hspan
      rw [hXi,hYj] at hspan'
      nlinarith
    apply mem_iUnion₂.mpr
    refine ⟨(i,j),mem_filter.mpr ⟨mem_product.mpr ⟨hi,hj⟩,hij⟩,?_⟩
    apply (mem_rareFastEvent ..).mpr
    refine ⟨q,es,?_,?_,?_,hdef⟩
    · simpa only [endpointVertex] using hq.trans hXi
    · simp only [endpointVertex]
      rw [he,hYj]
      ring
    · intro t ht
      have hz := endpointBox_into_rareFastRegion b A (R+2*(K+200)) hA k m J X Y hX hspan (hpath t ht)
      simpa only [hXi,hYj] using hz
  · exact Or.inl hg

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_arbitraryEndpoint_probability_bound (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K A R ε : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K) (hm : 0 < μ (direction b))
    (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (plus : Bool)
    (J : ℕ) (hJ : 1 ≤ J) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S D : ℝ, 1 ≤ S ∧ 0 < D ∧ ∀ k m : ℕ,
      J ≤ gridLastLevel m → gridLastLevel m ≤ k → S ≤ (2 : ℝ)^k →
      D*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) →
      2*endpointExtensionError K k J+2*|extremeSlope μ b plus| ≤ ε*(2 : ℝ)^k/2 →
      (2*R*|extremeSlope μ b plus| /(μ (direction b)))*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) →
      P.real {ω | (fun e => τ e ω) ∈
        arbitraryEndpointEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε k m} ≤
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b)) K A R k m J}+
        ((coarsePairIndices A J).card : ℝ)*κ := by
  let _ := henv.probability
  obtain ⟨S,D,hS,hD,hbound⟩ := exponential_coarsePair_bound henv μ hμ ht b A (R+2*(K+200)) ε
    hb hA (by linarith) hε plus J κ hκ
  refine ⟨S,D,hS,hD,?_⟩
  intro k m hJl hlast hs hd herror hscale
  let G : Set Ω := {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b)) K A R k m J}
  let E (ij : ℤ×ℤ) : Set Ω := {ω | (fun e => τ e ω) ∈
    coarsePairEvent b (μ (direction b)) (extremeSlope μ b plus) A (R+2*(K+200)) ε k m J ij}
  have hsub : {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
      (extremeSlope μ b plus) A R ε k m} ⊆ G ∪ ⋃ ij ∈ coarsePairIndices A J,E ij := by
    intro ω hω
    have hh := arbitraryEndpointEvent_coarse_cover b (μ (direction b)) K A R (extremeSlope μ b plus)
      ε hK hm hA.le hR.le hε k m J hJ hJl hlast herror hscale hω
    rcases hh with hh | hh
    · exact Or.inl hh
    · obtain ⟨ij,hij,he⟩ := mem_iUnion₂.mp hh
      exact Or.inr (mem_iUnion₂.mpr ⟨ij,hij,he⟩)
  calc
    _ ≤ P.real (G ∪ ⋃ ij ∈ coarsePairIndices A J,E ij) :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
    _ ≤ P.real G+P.real (⋃ ij ∈ coarsePairIndices A J,E ij) := measureReal_union_le _ _
    _ ≤ P.real G+∑ ij ∈ coarsePairIndices A J,P.real (E ij) :=
      add_le_add le_rfl (measureReal_biUnion_finset_le _ _)
    _ ≤ P.real G+∑ _ij ∈ coarsePairIndices A J,κ :=
      add_le_add le_rfl (sum_le_sum (fun ij hij => (hbound k m hs hd ij hij).le))
    _ = _ := by simp [G]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointLimit
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_arbitraryEndpoint_tendsto_of_grids_oai {ι : Type*} {l : Filter ι}
    (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K A R ε q₀ : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (hq : 0 < q₀) (plus : Bool)
    (k m : ι → ℕ) (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
    (hm : ∀ᶠ i in l, m i ≤ 3*k i)
    (hgrid : ∀ J : ℕ, 1 ≤ J → ∀ᶠ i in l,
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b)) K A R (k i) (m i) J} ≤
        gridFailureTail (gridIndexConstant A R) q₀ J) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
      (extremeSlope μ b plus) A R ε (k i) (m i)}) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    have htE : Tendsto (fun J => 32*(K+200)*endpointErrorTail J) atTop (𝓝 0) := by
      simpa using endpointErrorTail_tendsto.const_mul (32*(K+200))
    have htG := gridFailureTail_tendsto (gridIndexConstant A R) q₀ hq
    obtain ⟨J,hJE,hJG,hJ⟩ := ((htE.eventually (gt_mem_nhds (by linarith : 0 < ε/4))).and
      ((htG.eventually (gt_mem_nhds (by linarith : 0 < δ/2))).and (eventually_ge_atTop 1))).exists
    let M : ℝ := (coarsePairIndices A J).card
    have hM : 0 ≤ M := by positivity
    let κ : ℝ := δ/(2*(M+1))
    have hκ : 0 < κ := by dsimp [κ]; positivity
    have hκM : M*κ < δ/2 := by
      have hh : κ*(2*(M+1))=δ := by dsimp [κ]; field_simp
      nlinarith
    obtain ⟨S,D,_hS,_hD,hprob⟩ := exponential_arbitraryEndpoint_probability_bound henv μ hμ ht
      b K A R ε hb hK (norm_direction_pos μ hμ b) hA hR hε plus J hJ κ hκ
    have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hk
    have hd := endpoint_mesh_ratio_tendsto k m hratio J
    let C := 2*R*|extremeSlope μ b plus| /(μ (direction b))
    filter_upwards [endpoint_levels_eventually k m hk hratio hm J,
      endpoint_error_eventually k hk K (extremeSlope μ b plus) ε hε J hJE.le,
      hs.eventually (eventually_ge_atTop S),hd.eventually (eventually_ge_atTop D),
      hd.eventually (eventually_ge_atTop C),hgrid J hJ] with i hlev herr hsi hdi hci hgi
    have hs0 : (0 : ℝ) < 2^(k i) := by positivity
    have hp := hprob (k i) (m i) hlev.1 hlev.2 hsi ((le_div_iff₀ hs0).mp hdi) herr
      ((le_div_iff₀ hs0).mp hci)
    have hsmall : P.real {ω | (fun e => τ e ω) ∉
        gridConnectionsEvent b (μ (direction b)) K A R (k i) (m i) J} < δ/2 := hgi.trans_lt hJG
    change M*κ < δ/2 at hκM
    change _ ≤ _+M*κ at hp
    linarith

end PlanarFPP

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids_oai.{u_1, u_2} := @OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids_oai.{u_1, u_2}

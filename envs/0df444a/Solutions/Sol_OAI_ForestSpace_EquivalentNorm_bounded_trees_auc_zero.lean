-- Prove2me | solution 1 for OAI.ForestSpace.EquivalentNorm.bounded_trees_auc_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:00:20.937038+00:00
-- url     : https://prove2.me/submissions/2d7b8934-25f9-454f-b57c-8ff81f4f16fb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Renorming.lean:L256-L303
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.EquivalentNorm.bounded_trees_auc_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming

-- ---- from OAI.Analysis.ForestSpace.ModulusProofs ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ModulusDefinitions

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E}

 theorem cofinite_nontrivial (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    Nontrivial F.val := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hss
  let := hss
  let : FiniteDimensional ℝ F.val := Module.Finite.of_injective
    (0 : F.val →ₗ[ℝ] ℝ) (fun _ _ _ => Subsingleton.elim _ _)
  let : FiniteDimensional ℝ (E ⧸ F.val) := F.property.2
  exact hI (Module.Finite.of_submodule_quotient F.val)

 theorem cofinite_exists_unit (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    ∃ y : E, y ∈ F.val ∧ ‖y‖ = 1 := by
  let := cofinite_nontrivial hI F
  obtain ⟨y,hy⟩ := exists_norm_eq F.val zero_le_one
  exact ⟨y,y.property,hy⟩

 theorem cofiniteKernel {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] (f : E →L[ℝ] G) :
    IsClosed (f.toLinearMap.ker : Set E) ∧ FiniteDimensional ℝ (E ⧸ f.toLinearMap.ker) := by
  exact ⟨f.isClosed_ker, Module.Finite.equiv f.toLinearMap.quotKerEquivRange.symm⟩

end ModulusDefinitions

section ForestModulus
variable {V : Type} [PartialOrder V]

end ForestModulus

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Renorming ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section WeakNull
open Filter
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem weakNull_finiteDimensional {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] (d : ℕ → E) (hd : WeakNull d)
    (L : E →L[ℝ] G) : Tendsto (fun n => L (d n)) atTop (nhds 0) := by
  let b := (Module.finBasis ℝ G).equivFunL
  have hb : Tendsto (fun n => b (L (d n))) atTop (nhds 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hd ((ContinuousLinearMap.proj i).comp (b.toContinuousLinearMap.comp L))
  have hh := b.symm.continuous.continuousAt.tendsto.comp hb
  simpa only [Function.comp_def, b.symm_apply_apply, map_zero] using hh

 theorem weakNull_cofinite_approx (d : ℕ → E) (hd : WeakNull d)
    (F : Cofinite E) (ε : ℝ) (hε : 0 < ε) :
    ∃ j : ℕ, ∃ w : E, w ∈ F.val ∧ ‖w-d j‖ < ε := by
  let : IsClosed (F.val : Set E) := F.property.1
  let : FiniteDimensional ℝ (E ⧸ F.val) := F.property.2
  have hh := weakNull_finiteDimensional d hd F.val.mkQL
  obtain ⟨j,hj⟩ := (Metric.tendsto_atTop.mp hh (ε/2) (by positivity))
  have hj' : ‖F.val.mkQL (d j)‖ < ε/2 := by simpa using hj j le_rfl
  obtain ⟨v,hv,hnv⟩ := Submodule.Quotient.norm_mk_lt (F.val.mkQL (d j))
    (show 0 < ε/2 by positivity)
  refine ⟨j,d j-v, ?_, ?_⟩
  · exact (Submodule.Quotient.eq F.val).mp hv.symm
  · have he : d j-v-d j = -v := by abel
    rw [he, norm_neg]
    linarith

end WeakNull

section EquivalentNormModulus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {α β : ℝ} (R : EquivalentNorm E α β)

 include R in
 theorem EquivalentNorm.beta_pos : 0 < β := R.alpha_pos.trans_le R.alpha_le_beta
 theorem EquivalentNorm.nonneg (x : E) : 0 ≤ R.N x :=
  (mul_nonneg R.alpha_pos.le (norm_nonneg x)).trans (R.lower x)
 theorem EquivalentNorm.continuous : Continuous R.N := by
  let b : NNReal := ⟨β,R.beta_pos.le⟩
  apply Seminorm.continuous_of_le (q := b • normSeminorm ℝ E)
  · exact continuous_norm.const_smul b
  · intro x
    exact R.upper x

 theorem EquivalentNorm.cofinite_unit (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    ∃ y : E, y ∈ F.val ∧ R.N y = 1 := by
  obtain ⟨z,hz,hzn⟩ := cofinite_exists_unit hI F
  have hp : 0 < R.N z := (by simpa [hzn] using R.alpha_pos : 0 < α*‖z‖).trans_le (R.lower z)
  refine ⟨(R.N z)⁻¹ • z, F.val.smul_mem _ hz, ?_⟩
  rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']

 theorem EquivalentNorm.support {x : E} (hx : R.N x = 1) :
    ∃ φ : StrongDual ℝ E, φ x = 1 ∧ ∀ z : E, |φ z| ≤ R.N z := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let e := LinearEquiv.toSpanNonzeroSingleton ℝ E x hx0
  let f : Module.Dual ℝ (ℝ ∙ x) := e.symm.toLinearMap
  have hf : ∀ z : (ℝ ∙ x), ‖f z‖ ≤ R.N (z : E) := by
    intro z
    obtain ⟨c,rfl⟩ := e.surjective z
    change ‖e.symm (e c)‖ ≤ R.N (e c : E)
    rw [e.symm_apply_apply]
    change ‖c‖ ≤ R.N (c • x)
    rw [map_smul_eq_mul,hx,mul_one]
  obtain ⟨φ,hφ,hbound⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (ℝ ∙ x) f R.continuous hf
  refine ⟨φ, ?_, ?_⟩
  · have hh := hφ (e 1)
    change φ (e 1 : E) = e.symm (e 1) at hh
    rw [e.symm_apply_apply] at hh
    simpa only [e, LinearEquiv.toSpanNonzeroSingleton_apply, one_smul] using hh
  · intro z
    simpa only [Real.norm_eq_abs] using hbound z

 theorem EquivalentNorm.aucValues_nonempty (hI : ¬FiniteDimensional ℝ E)
    (t : ℝ) (x : E) (F : Cofinite E) : (aucValues E R.N t x F).Nonempty := by
  obtain ⟨y,hy,hyn⟩ := R.cofinite_unit hI F
  exact ⟨_,y,hy,hyn,rfl⟩

 theorem EquivalentNorm.aucValues_bddBelow (t : ℝ) (x : E) (F : Cofinite E) :
    BddBelow (aucValues E R.N t x F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y,hy,hyn,rfl⟩
  linarith [R.nonneg (x+t•y)]

 theorem EquivalentNorm.aucInner_le (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : R.N x = 1) (F : Cofinite E) :
    aucInner E R.N t x F ≤ t := by
  obtain ⟨y,hy,hyn⟩ := R.cofinite_unit hI F
  have hp := map_add_le_add R.N x (t•y)
  rw [hx,map_smul_eq_mul,Real.norm_of_nonneg ht,hyn,mul_one] at hp
  have hi := csInf_le (R.aucValues_bddBelow t x F) (show
    R.N (x+t•y)-1 ∈ aucValues E R.N t x F from ⟨y,hy,hyn,rfl⟩)
  exact hi.trans (by linarith)

 theorem EquivalentNorm.aucCenter_bddAbove (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : R.N x = 1) :
    BddAbove (Set.range (aucInner E R.N t x)) := by
  exact ⟨t, fun a ⟨F,hF⟩ => hF ▸ R.aucInner_le hI ht hx F⟩

 theorem EquivalentNorm.aucCenter_nonneg (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : R.N x = 1) :
    0 ≤ aucCenter E R.N t x := by
  obtain ⟨φ,hφ,hbound⟩ := R.support hx
  let F : Cofinite E := ⟨φ.toLinearMap.ker,cofiniteKernel φ⟩
  have hi : 0 ≤ aucInner E R.N t x F := by
    apply le_csInf (R.aucValues_nonempty hI t x F)
    rintro a ⟨y,hy,hyn,rfl⟩
    have hy' : φ y = 0 := hy
    have hb := hbound (x+t•y)
    rw [map_add,map_smul,hφ,hy',smul_zero,add_zero,abs_one] at hb
    linarith
  exact hi.trans (le_csSup (R.aucCenter_bddAbove hI ht hx) ⟨F,rfl⟩)

 theorem EquivalentNorm.aucModulus_nonneg (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ aucModulus E R.N t := by
  apply le_csInf
  · obtain ⟨x,hx,hxn⟩ := R.cofinite_unit hI (cofiniteTop E)
    exact ⟨_,x,hxn,rfl⟩
  · rintro a ⟨x,hx,rfl⟩
    exact R.aucCenter_nonneg hI ht hx

 theorem EquivalentNorm.aucModulus_le_center (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : R.N x = 1) :
    aucModulus E R.N t ≤ aucCenter E R.N t x := by
  apply csInf_le
  · exact ⟨0, fun a ⟨z,hz,he⟩ => he ▸ R.aucCenter_nonneg hI ht hz⟩
  · exact ⟨x,hx,rfl⟩

 theorem EquivalentNorm.subspace_gain (hI : ¬FiniteDimensional ℝ E)
    {t γ : ℝ} (ht : 0 < t) (hγ : γ < aucModulus E R.N t)
    {x : E} (hx : R.N x = 1) : ∃ F : Cofinite E,
    ∀ y : E, y ∈ F.val → R.N y = 1 → 1+γ ≤ R.N (x+t•y) := by
  have hh : γ < aucCenter E R.N t x := hγ.trans_le (R.aucModulus_le_center hI ht.le hx)
  obtain ⟨a,⟨F,rfl⟩,hF⟩ := (lt_csSup_iff (R.aucCenter_bddAbove hI ht.le hx)
    ⟨_,cofiniteTop E,rfl⟩).mp hh
  refine ⟨F, ?_⟩
  intro y hy hyn
  have hi := csInf_le (R.aucValues_bddBelow t x F)
    (show R.N (x+t•y)-1 ∈ aucValues E R.N t x F from ⟨y,hy,hyn,rfl⟩)
  change γ < sInf (aucValues E R.N t x F) at hF
  linarith

end EquivalentNormModulus

section TreeObstruction
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α β : ℝ} (R : EquivalentNorm E α β)

 theorem EquivalentNorm.gain_extended {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    {x : E} (hx : R.N x = 1) (F : Cofinite E)
    (hF : ∀ y : E, y ∈ F.val → R.N y = 1 → 1+γ ≤ R.N (x+t•y))
    {w : E} (hw : w ∈ F.val) (hwn : t ≤ R.N w) :
    1+γ ≤ R.N (x+w) := by
  have hp : 0 < R.N w := ht.trans_le hwn
  let c : ℝ := t / R.N w
  have hc : 0 < c := div_pos ht hp
  have hc1 : c ≤ 1 := (div_le_one hp).mpr hwn
  have hn : R.N ((R.N w)⁻¹ • w) = 1 := by
    rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
  have hg := hF ((R.N w)⁻¹ • w) (F.val.smul_mem _ hw) hn
  have he : x+t•((R.N w)⁻¹•w) = (1-c)•x+c•(x+w) := by
    simp only [smul_add, smul_smul, sub_smul, one_smul, c, div_eq_mul_inv]
    abel
  rw [he] at hg
  have hu := map_add_le_add R.N ((1-c)•x) (c•(x+w))
  rw [map_smul_eq_mul,map_smul_eq_mul,Real.norm_of_nonneg (sub_nonneg.mpr hc1),
    Real.norm_of_nonneg hc.le,hx,mul_one] at hu
  by_contra hh
  have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hc
  have hle := mul_le_mul_of_nonneg_right hc1 hγ
  nlinarith

 theorem EquivalentNorm.vector_gain (hI : ¬FiniteDimensional ℝ E)
    {t γ : ℝ} (ht : 0 < t) (hγ0 : 0 ≤ γ) (hγ : γ < aucModulus E R.N t)
    {u : E} (hu : 0 < R.N u) : ∃ F : Cofinite E,
    ∀ w : E, w ∈ F.val → t*R.N u ≤ R.N w →
      (1+γ)*R.N u ≤ R.N (u+w) := by
  have hn : R.N ((R.N u)⁻¹•u) = 1 := by
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le),inv_mul_cancel₀ hu.ne']
  obtain ⟨F,hF⟩ := R.subspace_gain hI ht hγ hn
  refine ⟨F, ?_⟩
  intro w hw hwn
  have hNw : t ≤ R.N ((R.N u)⁻¹•w) := by
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]
    exact (le_inv_mul_iff₀ hu).mpr (by simpa only [mul_comm] using hwn)
  have hg := R.gain_extended ht hγ0 hn F hF (F.val.smul_mem (R.N u)⁻¹ hw) hNw
  rw [← smul_add,map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)] at hg
  simpa only [mul_comm] using (le_inv_mul_iff₀ hu).mp hg

 theorem EquivalentNorm.child_gain (hI : ¬FiniteDimensional ℝ E)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < aucModulus E R.N (α/(2*β)))
    (u : E) (hu : ‖u‖ = 1) (v : ℕ → E)
    (hd : ∀ j, 1 ≤ ‖v j-u‖) (hweak : WeakNull (fun j => v j-u)) :
    ∃ j, R.N u+γ*α/2 ≤ R.N (v j) := by
  have huL : α ≤ R.N u := by simpa [hu] using R.lower u
  have huU : R.N u ≤ β := by simpa [hu] using R.upper u
  have hup : 0 < R.N u := R.alpha_pos.trans_le huL
  have ht : 0 < α/(2*β) := div_pos R.alpha_pos (mul_pos (by norm_num) R.beta_pos)
  obtain ⟨F,hF⟩ := R.vector_gain hI ht hγ0.le hγ hup
  let ε : ℝ := min (α/(2*β)) (γ*α/(2*β))
  have hε : 0 < ε := lt_min ht (div_pos (mul_pos hγ0 R.alpha_pos) (mul_pos (by norm_num) R.beta_pos))
  obtain ⟨j,w,hw,hclose⟩ := weakNull_cofinite_approx (fun j => v j-u) hweak F ε hε
  have herr : R.N (w-(v j-u)) < β*ε :=
    (R.upper _).trans_lt (mul_lt_mul_of_pos_left hclose R.beta_pos)
  have he1 : β*ε ≤ α/2 := by
    calc
      β*ε ≤ β*(α/(2*β)) := mul_le_mul_of_nonneg_left (min_le_left _ _) R.beta_pos.le
      _ = α/2 := by field_simp [R.beta_pos.ne']
  have he2 : β*ε ≤ γ*α/2 := by
    calc
      β*ε ≤ β*(γ*α/(2*β)) := mul_le_mul_of_nonneg_left (min_le_right _ _) R.beta_pos.le
      _ = γ*α/2 := by field_simp [R.beta_pos.ne']
  have hdL : α ≤ R.N (v j-u) :=
    (le_mul_of_one_le_right R.alpha_pos.le (hd j)).trans (R.lower _)
  have hwL : α/2 ≤ R.N w := by
    have hh := map_sub_le_add R.N w (w-(v j-u))
    have he : w-(w-(v j-u)) = v j-u := by abel
    rw [he] at hh
    linarith
  have hth : α/(2*β)*R.N u ≤ α/2 := by
    calc
      α/(2*β)*R.N u ≤ α/(2*β)*β := mul_le_mul_of_nonneg_left huU ht.le
      _ = α/2 := by field_simp [R.beta_pos.ne']
  have hgain := hF w hw (hth.trans hwL)
  have hupper := map_add_le_add R.N (v j) (w-(v j-u))
  have he : v j+(w-(v j-u)) = u+w := by abel
  rw [he] at hupper
  refine ⟨j, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left huL hγ0.le]

/-- The obstruction scale for bounded norm-one paths and
norm-one (or larger) weakly null child increments. An additive form of the
uniform gain is enough for the final finite-height contradiction. -/
 theorem EquivalentNorm.bounded_trees_auc_zero (hI : ¬FiniteDimensional ℝ E)
    (u : ℕ → List ℕ → E)
    (hu : ∀ h ≥ 1, ∀ s : List ℕ, s.length ≤ h → ‖u h s‖ = 1)
    (hd : ∀ h ≥ 1, ∀ s : List ℕ, s.length < h → ∀ j,
      1 ≤ ‖u h (s++[j])-u h s‖)
    (hweak : ∀ h ≥ 1, ∀ s : List ℕ, s.length < h →
      WeakNull (fun j => u h (s++[j])-u h s)) :
    aucModulus E R.N (α/(2*β)) = 0 := by
  have ht : 0 < α/(2*β) := div_pos R.alpha_pos (mul_pos (by norm_num) R.beta_pos)
  apply le_antisymm ?_ (R.aucModulus_nonneg hI ht.le)
  by_contra hh
  have hpos : 0 < aucModulus E R.N (α/(2*β)) := lt_of_not_ge hh
  let γ : ℝ := aucModulus E R.N (α/(2*β))/2
  have hγ0 : 0 < γ := half_pos hpos
  have hγ : γ < aucModulus E R.N (α/(2*β)) := half_lt_self hpos
  let δ : ℝ := γ*α/2
  have hδ : 0 < δ := div_pos (mul_pos hγ0 R.alpha_pos) (by norm_num)
  obtain ⟨h,hh⟩ := exists_nat_gt (β/δ)
  have hb : β < (h:ℝ)*δ := (div_lt_iff₀ hδ).mp hh
  have hh1 : 1 ≤ h := by
    by_contra hn
    have : h = 0 := by omega
    subst h
    simp at hb
    linarith [R.beta_pos]
  have hg : ∀ n : ℕ, n ≤ h → ∃ s : List ℕ,
      s.length = n ∧ (n:ℝ)*δ ≤ R.N (u h s) := by
    intro n hn
    induction n with
    | zero => exact ⟨[],rfl,by simp [R.nonneg]⟩
    | succ n ih =>
      obtain ⟨s,hs,hNs⟩ := ih (by omega)
      have hslt : s.length < h := by omega
      obtain ⟨j,hj⟩ := R.child_gain hI hγ0 hγ (u h s)
        (hu h hh1 s (by omega)) (fun j => u h (s++[j]))
        (hd h hh1 s hslt) (hweak h hh1 s hslt)
      refine ⟨s++[j],by simp [hs], ?_⟩
      push_cast

      dsimp [δ] at hNs ⊢
      linarith
  obtain ⟨s,hs,hNs⟩ := hg h le_rfl
  have hU := R.upper (u h s)
  rw [hu h hh1 s (by omega)] at hU
  linarith

end TreeObstruction

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.EquivalentNorm.bounded_trees_auc_zero := @_root_.OAI.ForestSpace.EquivalentNorm.bounded_trees_auc_zero

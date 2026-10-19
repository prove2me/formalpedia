-- Prove2me | solution 1 for OAI.ContinuumTemperature.exists_constructionData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:06:06.692637+00:00
-- url     : https://prove2.me/submissions/b3ebacb9-8722-45b2-b66e-5fdf1828510a

import Mathlib
import Definitions.Def_ContinuumTransition
import Definitions.Def_OAIQWCT000
import Theorems.Thm_OAI_ContinuumTemperature_core_pressure_locally_uniform
import Theorems.Thm_OAI_ContinuumTemperature_core_transform_locally_uniform
import Theorems.Thm_OAI_ContinuumTemperature_physical_kac_approximate

section
-- module Solutions.OAIQW_ContinuumTemperature.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section

open scoped Topology BigOperators
open Set Filter

noncomputable section

namespace ContinuumTemperature

theorem strict_face_support {K : Set Parameter} {ξ v : Parameter} {β : ℝ}
    (hmax : ∀ u ∈ K, quadraticObjective ξ u β ≤ quadraticObjective ξ v β)
    {u : Parameter} (hu : u ∈ K) :
    β / 2 * (u.2 - v.2) ^ 2 ≤
      ξ.1 * (v.1 - u.1) + (ξ.2 + β * v.2) * (v.2 - u.2) := by
  have h := hmax u hu
  dsimp [quadraticObjective] at h
  nlinarith [sq_nonneg (u.2 - v.2)]

theorem weighted_maximizer_densities {ι : Type u_1} [Fintype ι]
    {K : Set Parameter} {ξ v : Parameter} {β : ℝ}
    (hβ : 0 < β) (a : ι → ℝ) (z : ι → Parameter)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hz : ∀ i, z i ∈ K) (hv : ∑ i, a i • z i = v)
    (hmax : ∀ u ∈ K, quadraticObjective ξ u β ≤ quadraticObjective ξ v β) :
    ∀ i, a i ≠ 0 → (z i).2 = v.2 := by
  have hfst : ∑ i, a i * (z i).1 = v.1 := by
    simpa only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using congrArg Prod.fst hv
  have hsnd : ∑ i, a i * (z i).2 = v.2 := by
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using congrArg Prod.snd hv
  let gap : ι → ℝ := fun i =>
    ξ.1 * (v.1 - (z i).1) + (ξ.2 + β * v.2) * (v.2 - (z i).2)
  have hgap : ∀ i, 0 ≤ gap i := by
    intro i
    exact le_trans (mul_nonneg (by positivity) (sq_nonneg _))
      (strict_face_support hmax (hz i))
  have hsum : ∑ i, a i * gap i = 0 := by
    calc
      ∑ i, a i * gap i =
          ∑ i, (ξ.1 * (a i * v.1 - a i * (z i).1) +
            (ξ.2 + β * v.2) * (a i * v.2 - a i * (z i).2)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [gap]
        ring
      _ = ξ.1 * ((∑ i, a i) * v.1 - ∑ i, a i * (z i).1) +
          (ξ.2 + β * v.2) * ((∑ i, a i) * v.2 - ∑ i, a i * (z i).2) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = 0 := by rw [ha1, hfst, hsnd]; ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => mul_nonneg (ha i) (hgap i))).mp hsum
  intro i hi
  have hgi : gap i = 0 := (mul_eq_zero.mp (hzero i (Finset.mem_univ i))).resolve_left hi
  have hstrict := strict_face_support hmax (hz i)
  change β / 2 * ((z i).2 - v.2) ^ 2 ≤ gap i at hstrict
  rw [hgi] at hstrict
  have hs : ((z i).2 - v.2) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((z i).2 - v.2)]
  nlinarith [sq_nonneg ((z i).2 - v.2)]

theorem quadratic_maximizer_mem_group {κ : Type u_1} (K : κ → Set Parameter)
    (hconv : ∀ i, Convex ℝ (K i))
    (hsep : ∀ i j, i ≠ j → Disjoint (Prod.snd '' K i) (Prod.snd '' K j))
    {ξ v : Parameter} {β : ℝ} (hβ : 0 < β)
    (hv : v ∈ convexHull ℝ (⋃ i, K i))
    (hmax : ∀ u ∈ convexHull ℝ (⋃ i, K i),
      quadraticObjective ξ u β ≤ quadraticObjective ξ v β) : v ∈ ⋃ i, K i := by
  classical
  obtain ⟨ι, inst, a, z, ha, ha1, hz, hzv⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  let _ := inst
  have hd := weighted_maximizer_densities hβ a z ha ha1
    (fun i => subset_convexHull ℝ _ (hz i)) hzv hmax
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ha1 ▸ one_ne_zero)
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hz i₀)
  have hzk : ∀ i, a i ≠ 0 → z i ∈ K k := by
    intro i hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hz i)
    have hjk : j = k := by
      by_contra hne
      exact Set.disjoint_left.mp (hsep j k hne)
        ⟨z i, hj, hd i hi⟩ ⟨z i₀, hk, hd i₀ hi₀⟩
    simpa only [hjk] using hj
  let z' : ι → Parameter := fun i => if a i = 0 then z i₀ else z i
  have hz' : ∀ i, z' i ∈ K k := by
    intro i
    dsimp [z']
    split_ifs with hi
    · exact hk
    · exact hzk i hi
  have hsumeq : ∑ i, a i • z' i = v := by
    rw [← hzv]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [z']
    split_ifs with hi
    · simp [hi]
    · rfl
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  rw [← hsumeq]
  exact (hconv k).sum_mem (fun i _ => ha i) ha1 (fun i _ => hz' i)

theorem fenchel_eq_of_support {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {β h s d : ℝ}
    (hβ : 0 < β) (hd : 0 ≤ d) (hv : Supports Q (β, h) (s, d)) :
    H β d = h * d - Q (β, h) := by
  have hL := hH β d hβ hd
  apply le_antisymm
  · apply hL.2
    rintro _ ⟨z, rfl⟩
    have hz := hv (β, z) hβ
    dsimp at hz
    nlinarith
  · exact hL.1 (mem_range_self h)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConvexSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology
open Filter Set
noncomputable section
namespace ContinuumTemperature

lemma supports_iff_supportOn {F : Parameter → ℝ} {x v : Parameter} :
    Supports F x v ↔ SupportOn pressureDomain F x v := by
  simp only [Supports, SupportOn, pDot, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h y hy <;> have := h y hy <;> linarith

lemma linear_parameter_eq (L : Parameter →L[ℝ] ℝ) (x : Parameter) :
    L x = x.1*L (1,0)+x.2*L (0,1) := by
  have he : x = x.1 • ((1,0) : Parameter) + x.2 • ((0,1) : Parameter) := by ext <;> simp
  rw [he,L.map_add,L.map_smul,L.map_smul]
  simp only [smul_eq_mul,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,mul_one,mul_zero,zero_add,add_zero]

lemma linear_epigraph_eq (L : (Parameter × ℝ) →L[ℝ] ℝ) (x : Parameter) (r : ℝ) :
    L (x,r) = x.1*L ((1,0),0)+x.2*L ((0,1),0)+r*L (0,1) := by
  have he : (x,r) = x.1 • (((1,0),0) : Parameter × ℝ) +
      x.2 • (((0,1),0) : Parameter × ℝ) + r • ((0,1) : Parameter × ℝ) := by ext <;> simp
  rw [he,L.map_add,L.map_add,L.map_smul,L.map_smul,L.map_smul]
  simp only [smul_eq_mul]

lemma convex_exists_support {S : Set Parameter} (hS : IsOpen S) {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x : Parameter} (hx : x ∈ S) :
    ∃ v, SupportOn S F x v := by
  have hcont := hF.continuousOn hS
  have hopen : IsOpen {p : Parameter × ℝ | p.1 ∈ S ∧ F p.1 < p.2} := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hh : ContinuousAt (fun q : Parameter × ℝ => F q.1) p :=
      (hcont.continuousAt (hS.mem_nhds hp.1)).comp continuousAt_fst
    have hlt := hh.eventually_lt continuousAt_snd hp.2
    filter_upwards [(hS.preimage continuous_fst).mem_nhds hp.1,hlt] with q hq hq'
    exact ⟨hq,hq'⟩
  obtain ⟨L,hL⟩ := geometric_hahn_banach_point_open hF.convex_strict_epigraph hopen
    (x := (x,F x)) (by simp)
  let a := L (0,1)
  let b := L ((1,0),0)
  let c := L ((0,1),0)
  have ha : 0 < a := by
    have hh := hL (x,F x+1) ⟨hx,by linarith⟩
    rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L x (F x+1)] at hh
    dsimp [a]
    nlinarith
  have hle : ∀ y ∈ S, L (x,F x) ≤ L (y,F y) := by
    intro y hy
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hL (y,F y+ε/a) ⟨hy,by have := div_pos hε ha; linarith⟩
    rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L y (F y+ε/a)] at hh
    rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L y (F y)]
    change x.1*b+x.2*c+F x*a < y.1*b+y.2*c+(F y+ε/a)*a at hh
    change x.1*b+x.2*c+F x*a ≤ y.1*b+y.2*c+F y*a+ε
    have he : (F y+ε/a)*a = F y*a+ε := by field_simp
    rw [he] at hh
    linarith only [hh]
  refine ⟨(-b/a,-c/a),?_⟩
  intro y hy
  have hh := hle y hy
  rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L y (F y)] at hh
  change F x + ((-b/a)*(y.1-x.1)+(-c/a)*(y.2-x.2)) ≤ F y
  apply (mul_le_mul_iff_left₀ ha).mp
  dsimp [a,b,c] at *
  field_simp
  nlinarith

lemma subgradients_closed (S : Set Parameter) (F : Parameter → ℝ) (x : Parameter) :
    IsClosed (subgradients S F x) := by
  simp only [subgradients,SupportOn,ofPred_forall]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  exact isClosed_le (by unfold pDot; fun_prop) continuous_const

lemma subgradients_convex (S : Set Parameter) (F : Parameter → ℝ) (x : Parameter) :
    Convex ℝ (subgradients S F x) := by
  intro v hv w hw a b ha hb hab y hy
  have hv' := hv y hy
  have hw' := hw y hy
  have hscaled := add_le_add (mul_le_mul_of_nonneg_left hv' ha) (mul_le_mul_of_nonneg_left hw' hb)
  have hFx := congrArg (fun q : ℝ => q*F x) hab
  have hFy := congrArg (fun q : ℝ => q*F y) hab
  dsimp [pDot] at *
  nlinarith only [hscaled,hFx,hFy]

lemma supportOn_limit {ι : Type u_1} {l : Filter ι} [l.NeBot]
    {S : Set Parameter} {F : Parameter → ℝ} (hF : ContinuousOn F S)
    {x : Parameter} (hx : x ∈ S) {X V : ι → Parameter} {v : Parameter}
    (hX : Tendsto X l (𝓝 x)) (hV : Tendsto V l (𝓝 v))
    (hXS : ∀ᶠ i in l, X i ∈ S) (h : ∀ᶠ i in l, SupportOn S F (X i) (V i)) :
    SupportOn S F x v := by
  intro y hy
  have hf := hF x hx |>.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hX,hXS⟩)
  have hX1 : Tendsto (fun i => (X i).1) l (𝓝 x.1) := (continuous_fst.tendsto x).comp hX
  have hX2 : Tendsto (fun i => (X i).2) l (𝓝 x.2) := (continuous_snd.tendsto x).comp hX
  have hV1 : Tendsto (fun i => (V i).1) l (𝓝 v.1) := (continuous_fst.tendsto v).comp hV
  have hV2 : Tendsto (fun i => (V i).2) l (𝓝 v.2) := (continuous_snd.tendsto v).comp hV
  have hvv : Tendsto (fun i => pDot (V i) (y-X i)) l (𝓝 (pDot v (y-x))) := by
    unfold pDot
    exact (hV1.mul (tendsto_const_nhds.sub hX1)).add
      (hV2.mul (tendsto_const_nhds.sub hX2))
  exact le_of_tendsto (hf.add hvv) (h.mono fun i hi => hi y hy)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConvexUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology NNReal
open Filter Set Metric
noncomputable section
namespace ContinuumTemperature

variable {E : Type u_1} {ι : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {l : Filter ι} [l.NeBot] {S : Set E} {F : ι → E → ℝ} {f : E → ℝ}

omit [l.NeBot] in

lemma eventually_convex_lipschitz (hS : IsOpen S)
    (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x))) {x : E} (hx : x ∈ S) :
    ∃ r > 0, ball x r ⊆ S ∧ ∃ C : ℝ≥0, ∀ᶠ i in l, LipschitzOnWith C (F i) (ball x r) := by
  obtain ⟨b,hxb,hbS⟩ := exists_mem_interior_convexHull_affineBasis (hS.mem_nhds hx)
  obtain ⟨M,hM⟩ := (finite_range (fun j => f (b j))).bddAbove
  let C : ℝ := |M|+|f x|+2
  have hC : 0 < C := by dsimp [C]; positivity
  have hv : ∀ᶠ i in l, ∀ j, F i (b j) ≤ C := by
    apply eventually_all.mpr
    intro j
    have hb : b j ∈ S := hbS (subset_convexHull ℝ _ (mem_range_self j))
    filter_upwards [(hlim _ hb).eventually_lt_const (show f (b j) < f (b j)+1 by linarith)] with i hi
    have hm := hM (mem_range_self j)
    have hMle := le_abs_self M
    have hxf := abs_nonneg (f x)
    dsimp [C]
    linarith
  have hxlower : ∀ᶠ i in l, -C ≤ F i x := by
    filter_upwards [(hlim _ hx).eventually_const_lt (show f x-1 < f x by linarith)] with i hi
    have hxabs := neg_abs_le (f x)
    have hm := abs_nonneg M
    dsimp [C]
    linarith
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hxb)
  have hrh : ball x r ⊆ convexHull ℝ (range b) := hrb.trans interior_subset
  refine ⟨r/2,by positivity,(ball_subset_ball (by linarith : r/2 ≤ r)).trans (hrh.trans hbS),
    (2*(3*C)/(r/2)).toNNReal,?_⟩
  filter_upwards [hconv,hv,hxlower] with i hi hiv hix
  have hub : ∀ y ∈ convexHull ℝ (range b), F i y ≤ C := by
    have hh : convexHull ℝ (range b) ⊆ {y ∈ S | F i y ≤ C} :=
      convexHull_min (by rintro y ⟨j,rfl⟩; exact ⟨hbS (subset_convexHull ℝ _ (mem_range_self j)),hiv j⟩)
        (hi.convex_le C)
    exact fun y hy => (hh hy).2
  have habs : ∀ y, dist y x < r → |F i y| ≤ 3*C := by
    intro y hy
    have hyb := hrh hy
    have hreflect : 2 • x-y ∈ ball x r := by
      rw [mem_ball,dist_eq_norm_sub,show 2 • x-y-x = x-y by module,norm_sub_rev]
      simpa only [dist_eq_norm_sub] using hy
    have huby := hub y hyb
    have hubr := hub _ (hrh hreflect)
    have hmid := hi.2 (hbS hyb) (hbS (hrh hreflect))
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    have he : (1/2:ℝ) • y + (1/2:ℝ) • (2 • x-y) = x := by module
    rw [he] at hmid
    simp only [smul_eq_mul] at hmid
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hL := (hi.subset (hrh.trans hbS) (convex_ball x r)).lipschitzOnWith_of_abs_le
    (show 0 < r/2 by positivity) habs
  simpa only [show r-r/2=r/2 by ring] using hL

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CompactSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

lemma eventually_of_subseq (P : ℕ → Prop)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ n in atTop, P (φ (ψ n))) :
    ∀ᶠ n in atTop, P n := by
  by_contra hh
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hh)
  obtain ⟨ψ,_,hgood⟩ := h φ hφ
  obtain ⟨n,hn⟩ := hgood.exists
  exact hbad (ψ n) hn

lemma metric_tendsto_of_subseq {E : Type u_1} [PseudoMetricSpace E] {u : ℕ → E} {x : E}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n => u (φ (ψ n))) atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, dist (u n) x < ε := by
    apply eventually_of_subseq
    intro φ hφ
    obtain ⟨ψ,hψ,ht⟩ := h φ hφ
    exact ⟨ψ,hψ,ht.eventually (Metric.ball_mem_nhds x hε)⟩
  exact eventually_atTop.mp hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.SubgradientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology NNReal
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma supportOn_norm_le {S : Set Parameter} {F : Parameter → ℝ} {x v : Parameter}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ S) {C : ℝ≥0}
    (hL : LipschitzOnWith C F (ball x r)) (hv : SupportOn S F x v) : ‖v‖ ≤ C := by
  let δ := r/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ]; linarith
  have htest : ∀ e : Parameter, ‖e‖ = 1 → pDot v e ≤ C := by
    intro e he
    have hz : x+δ • e ∈ ball x r := by
      rw [mem_ball,dist_eq_norm_sub,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hδ,he,mul_one]
      exact hδr
    have hs := hv _ (hball hz)
    have hl := hL.dist_le_mul _ hz _ (mem_ball_self hr)
    rw [Real.dist_eq] at hl
    have hle := (le_abs_self (F (x+δ • e)-F x)).trans hl
    have hdist : dist (x+δ • e) x = δ := by
      rw [dist_eq_norm_sub,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hδ,he,mul_one]
    rw [hdist] at hle
    have heq : pDot v (x+δ • e-x) = δ*pDot v e := by dsimp [pDot]; ring
    rw [heq] at hs
    nlinarith
  have h1 := htest (1,0) (by simp [Prod.norm_def])
  have h2 := htest (-1,0) (by simp [Prod.norm_def])
  have h3 := htest (0,1) (by simp [Prod.norm_def])
  have h4 := htest (0,-1) (by simp [Prod.norm_def])
  rw [Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
  simp only [pDot,mul_one,mul_zero,mul_neg_one,zero_add,add_zero] at h1 h2 h3 h4
  exact ⟨abs_le.mpr ⟨by linarith,h1⟩,abs_le.mpr ⟨by linarith,h3⟩⟩

lemma supports_near_norm_le {S : Set Parameter} {F : Parameter → ℝ} {x y v : Parameter}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ S) {C : ℝ≥0}
    (hL : LipschitzOnWith C F (ball x r)) (hy : y ∈ ball x (r/2))
    (hv : SupportOn S F y v) : ‖v‖ ≤ C := by
  have hsub : ball y (r/2) ⊆ ball x r := by
    intro z hz
    exact lt_of_le_of_lt (dist_triangle z y x) (by change dist y x < r/2 at hy; change dist z y < r/2 at hz; linarith)
  exact supportOn_norm_le (by positivity : 0 < r/2) (hsub.trans hball) (hL.mono hsub) hv

lemma eventually_subgradients_bounded {ι : Type u_1} {l : Filter ι}
    {S : Set Parameter} (hS : IsOpen S) {F : ι → Parameter → ℝ} {f : Parameter → ℝ}
    (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x)))
    {X : ι → Parameter} {x : Parameter} (hx : x ∈ S) (hX : Tendsto X l (𝓝 x)) :
    ∃ C : ℝ≥0, ∀ᶠ i in l, ∀ v, SupportOn S (F i) (X i) v → ‖v‖ ≤ C := by
  obtain ⟨r,hr,hb,C,hC⟩ := eventually_convex_lipschitz hS hconv hlim hx
  refine ⟨C,?_⟩
  filter_upwards [hC,hX.eventually (ball_mem_nhds x (show 0 < r/2 by positivity))] with i hi hXi
  intro v hv
  exact supports_near_norm_le hr hb hi hXi hv

lemma supportOn_varying_limit {ι : Type u_1} {l : Filter ι} [l.NeBot]
    {S : Set Parameter} (hS : IsOpen S) {F : ι → Parameter → ℝ} {f : Parameter → ℝ}
    (hlim : TendstoLocallyUniformlyOn F f l S) (hf : ContinuousOn f S)
    {X V : ι → Parameter} {x v : Parameter} (hx : x ∈ S)
    (hX : Tendsto X l (𝓝 x)) (hV : Tendsto V l (𝓝 v))
    (h : ∀ᶠ i in l, SupportOn S (F i) (X i) (V i)) : SupportOn S f x v := by
  intro y hy
  have hfx := hlim.tendsto_comp (hf x hx) hx
    (tendsto_nhdsWithin_iff.2 ⟨hX,hX.eventually (hS.mem_nhds hx)⟩)
  have hd : Tendsto (fun i => pDot (V i) (y-X i)) l (𝓝 (pDot v (y-x))) := by
    exact (show Continuous (fun p : Parameter × Parameter => pDot p.1 (y-p.2)) by unfold pDot; fun_prop).tendsto
      (v,x) |>.comp (hV.prodMk_nhds hX)
  exact le_of_tendsto_of_tendsto (hfx.add hd) (hlim.tendsto_at hy)
    (h.mono fun i hi => hi y hy)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.SupportGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma pDot_continuous_left (ξ : Parameter) : Continuous (fun v : Parameter => pDot v ξ) := by
  unfold pDot
  fun_prop

lemma pDot_monotone_supports {S : Set Parameter} {F : Parameter → ℝ}
    {x y v w : Parameter} (hx : x ∈ S) (hy : y ∈ S)
    (hv : SupportOn S F x v) (hw : SupportOn S F y w) :
    pDot v (y-x) ≤ pDot w (y-x) := by
  have h1 := hv y hy
  have h2 := hw x hx
  dsimp [pDot] at *
  linarith

theorem support_generators_closedHull {S : Set Parameter} (hS : IsOpen S)
    {F : Parameter → ℝ} (hF : ConvexOn ℝ S F) (A : Parameter → Set Parameter)
    (hAsub : ∀ x ∈ S, A x ⊆ subgradients S F x)
    (hAne : ∀ x ∈ S, (A x).Nonempty)
    (hAcl : ∀ {X V : ℕ → Parameter} {x v : Parameter}, x ∈ S →
      Tendsto X atTop (𝓝 x) → Tendsto V atTop (𝓝 v) →
      (∀ n, X n ∈ S) → (∀ n, V n ∈ A (X n)) → v ∈ A x)
    {x : Parameter} (hx : x ∈ S) :
    subgradients S F x = closedConvexHull ℝ (A x) := by
  classical
  apply subset_antisymm
  · intro w hw
    by_contra hn
    obtain ⟨L,c,hL,hc⟩ := geometric_hahn_banach_closed_point
      (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull hn
    let ξ : Parameter := (L (1,0),L (0,1))
    let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
    have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
    have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    let X : ℕ → Parameter := fun n => x+ε n • ξ
    have hX : Tendsto X atTop (𝓝 x) := by
      simpa only [zero_smul,add_zero] using tendsto_const_nhds.add (hεlim.smul_const ξ)
    have hXS : ∀ᶠ n in atTop, X n ∈ S := hX.eventually (hS.mem_nhds hx)
    let Y : ℕ → Parameter := fun n => if X n ∈ S then X n else x
    have hYS : ∀ n, Y n ∈ S := by intro n; dsimp [Y]; split_ifs with h; exact h; exact hx
    have hYX : Y =ᶠ[atTop] X := hXS.mono fun n hn => ite_eq_left hn
    have hY : Tendsto Y atTop (𝓝 x) := hX.congr' hYX.symm
    choose V hV using fun n => hAne (Y n) (hYS n)
    obtain ⟨C,hC⟩ := eventually_subgradients_bounded (l := atTop) hS
      (F := fun _ : ℕ => F) (Eventually.of_forall fun _ => hF)
      (fun _ _ => tendsto_const_nhds) hx hY
    have hb : ∀ᶠ n in atTop, V n ∈ closedBall (0 : Parameter) C := by
      filter_upwards [hC] with n hn
      simpa only [mem_closedBall,dist_zero_right] using hn (V n) (hAsub _ (hYS n) (hV n))
    obtain ⟨v,_,φ,hφ,hvlim⟩ := (isCompact_closedBall (0 : Parameter) C).tendsto_subseq' hb.frequently
    have hvA := hAcl hx (hY.comp hφ.tendsto_atTop) hvlim
      (fun n => hYS (φ n)) (fun n => hV (φ n))
    have hd : pDot w ξ ≤ pDot v ξ := by
      apply ge_of_tendsto ((pDot_continuous_left ξ).tendsto v |>.comp hvlim)
      filter_upwards [hφ.tendsto_atTop.eventually hYX] with n hn
      have hm := pDot_monotone_supports hx (hYS (φ n)) hw (hAsub _ (hYS (φ n)) (hV (φ n)))
      rw [hn] at hm
      have he (z : Parameter) : pDot z (X (φ n)-x) = ε (φ n)*pDot z ξ := by dsimp [pDot,X]; ring
      rw [he,he] at hm
      change pDot w ξ ≤ pDot (V (φ n)) ξ
      exact (mul_le_mul_iff_right₀ (hε (φ n))).mp (by simpa only [mul_comm] using hm)
    have hLv := hL v (subset_closedConvexHull hvA)
    have he (z : Parameter) : L z = pDot z ξ := by exact linear_parameter_eq L z
    rw [he] at hLv hc
    linarith
  · exact closedConvexHull_min (hAsub x hx) (subgradients_convex S F x) (subgradients_closed S F x)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.RadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

noncomputable section
open scoped ContDiff

theorem baseKernel_nonneg (x : Space) : 0 ≤ baseKernel x := Real.smoothTransition.nonneg _

theorem baseKernel_eq_one {x : Space} (hx : ‖x‖ ≤ 1 / 2) : baseKernel x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem baseKernel_eq_zero {x : Space} (hx : 1 ≤ ‖x‖) : baseKernel x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem contDiff_baseKernel : ContDiff ℝ ∞ baseKernel := by
  have heq : baseKernel = fun x : Space =>
      (ContDiffBumpBase.ofInnerProductSpace Space).toFun 2 ((2 : ℝ) • x) := by
    funext x
    norm_num [baseKernel, ContDiffBumpBase.ofInnerProductSpace, norm_smul]
  rw [heq]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hmem : ((2 : ℝ), (2 : ℝ) • x) ∈ Ioi (1 : ℝ) ×ˢ (Set.univ : Set Space) := by
    norm_num
  have hdiff := (ContDiffBumpBase.ofInnerProductSpace Space).smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
  have hcomp := hdiff.comp x (contDiffAt_const.prodMk
    (ContDiffAt.const_smul (2 : ℝ) contDiffAt_id) :
      ContDiffAt ℝ ∞ (fun y : Space => ((2 : ℝ), (2 : ℝ) • y)) x)
  exact hcomp

theorem hasCompactSupport_baseKernel : HasCompactSupport baseKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  exact baseKernel_eq_zero (by simpa using (not_lt.mp (fun h => hx (by simpa using h.le))))

theorem integrable_baseKernel : Integrable baseKernel :=
  contDiff_baseKernel.continuous.integrable_of_hasCompactSupport hasCompactSupport_baseKernel

theorem integral_baseKernel_pos : 0 < ∫ x : Space, baseKernel x := by
  rw [integral_pos_iff_support_of_nonneg baseKernel_nonneg integrable_baseKernel]
  have hball : (Metric.ball (0 : Space) (1 / 2 : ℝ)).Nonempty := ⟨0, by norm_num⟩
  apply lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume hball)
  apply measure_mono
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa using hx
  rw [Function.mem_support, baseKernel_eq_one hn.le]
  norm_num

theorem kernelProfile_nonneg (r : ℝ) : 0 ≤ kernelProfile r :=
  div_nonneg (Real.smoothTransition.nonneg _) integral_baseKernel_pos.le

theorem kernelProfile_le (r : ℝ) : kernelProfile r ≤ 1 / (∫ x : Space, baseKernel x) := by
  exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) integral_baseKernel_pos.le

theorem continuous_kernelProfile : Continuous kernelProfile := by
  unfold kernelProfile
  exact (Real.smoothTransition.continuous.comp (continuous_const.sub
    (continuous_const.mul continuous_id))).div_const _

theorem kernelProfile_zero {r : ℝ} (hr : 1 ≤ r) : kernelProfile r = 0 := by
  unfold kernelProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

theorem scaledKernelProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledKernelProfile R r :=
  mul_nonneg (by positivity) (kernelProfile_nonneg _)

theorem scaledKernelProfile_le {R : ℝ} (hR : 0 < R) (r : ℝ) :
    scaledKernelProfile R r ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := by
  dsimp [scaledKernelProfile]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (kernelProfile_le (r / R))
    (by positivity : (0 : ℝ) ≤ R⁻¹ ^ 3)

theorem scaledKernelProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledKernelProfile R r = 0 := by
  unfold scaledKernelProfile
  rw [kernelProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)), mul_zero]

theorem continuous_scaledKernelProfile (R : ℝ) : Continuous (scaledKernelProfile R) := by
  exact continuous_const.mul (continuous_kernelProfile.comp (continuous_id.div_const _))

theorem kernelHeight_pos : 0 < kernelHeight := one_div_pos.mpr integral_baseKernel_pos

theorem scaledKernelProfile_le_height {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    scaledKernelProfile R r ≤ kernelHeight := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := scaledKernelProfile_le hRp r
    _ ≤ kernelHeight := by
      unfold kernelHeight
      apply div_le_div_of_nonneg_right _ integral_baseKernel_pos.le
      exact pow_le_one₀ (inv_nonneg.mpr hRp.le) (inv_le_one_of_one_le₀ hR)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem summable_attraction_terms {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    Summable (fun j => σ j * scaledKernelProfile (R j) r) := by
  apply (hs.mul_right kernelHeight).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem attraction_nonneg {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (r : ℝ) :
    0 ≤ attraction t σ R r := by
  apply mul_nonneg ht
  exact tsum_nonneg (fun j => mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))

theorem continuous_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Continuous (attraction t σ R) := by
  apply continuous_const.mul
  apply continuous_tsum (fun j => continuous_const.mul (continuous_scaledKernelProfile (R j)))
    (hs.mul_right kernelHeight)
  intro j r
  change ‖σ j * scaledKernelProfile (R j) r‖ ≤ σ j * kernelHeight
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem coreProfile_eq_zero {t r : ℝ} (ht : 1 < t) (hr : 1 ≤ r) :
    coreProfile t r = 0 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : (1 + shellDelta) * Real.exp (-t) < 1 := by
    have ht' : Real.exp t > 1 + t := by simpa only [add_comm] using (Real.add_one_lt_exp (by linarith : t ≠ 0))
    rw [Real.exp_neg]
    unfold shellDelta
    apply (mul_inv_lt_iff₀ (Real.exp_pos t)).mpr
    linarith
  unfold coreProfile
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (not_lt.mpr hr)]

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem measurable_coreProfile (t : ℝ) : Measurable (coreProfile t) := by
  unfold coreProfile
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.add ((measurable_const.div measurable_id).pow_const 12))
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem coreProfile_nonneg (t r : ℝ) : 0 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs <;> positivity

theorem coreProfile_le {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (t : ℝ) :
    coreProfile t r ≤ t ^ 2 + (Real.exp (-t) / a) ^ 12 := by
  have hdiv : Real.exp (-t) / r ≤ Real.exp (-t) / a :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le ha har
  have hp := pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le (ha.le.trans har)) hdiv 12
  unfold coreProfile
  split_ifs <;> nlinarith [sq_nonneg t, even_two_mul 6 |>.pow_nonneg (Real.exp (-t) / a)]

theorem measurable_physicalProfile (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Measurable (physicalProfile t σ R) :=
  (measurable_coreProfile t).sub (continuous_attraction t hσ hR hs).measurable

theorem measurable_radialPotential {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (radialPotential φ) := by
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_coe_real_ereal.comp (hφ.comp measurable_norm)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

open scoped InnerProductSpace

theorem affineIndependent_of_sq_dist_close {E : Type u_1} {ι : Type u_2}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v : ι → E) {a ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ε * Fintype.card ι < a)
    (hdist : ∀ i j, i ≠ j → |‖v i - v j‖ ^ 2 - a| ≤ ε) :
    AffineIndependent ℝ v := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.univ.weightedVSub_eq_linear_combination hw] at hv
  have hid := inner_sum_smul_sum_smul_of_sum_eq_zero v hw v hw
  rw [hv, inner_zero_left] at hid
  have hzero : (∑ i, ∑ j, w i * w j * ‖v i - v j‖ ^ 2) = 0 := by
    simp only [← sq] at hid
    linarith
  have hpair (i j : ι) :
      w i * w j * ‖v i - v j‖ ^ 2 ≤
        a * w i * w j - (if i = j then a * w i ^ 2 else 0) +
          ε / 2 * (w i ^ 2 + w j ^ 2) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, ↓reduceIte]
      nlinarith [mul_nonneg hε (sq_nonneg (w i))]
    · rw [ite_eq_right hij]
      have habs : w i * w j * (‖v i - v j‖ ^ 2 - a) ≤ |w i * w j| * ε := by
        calc
          _ ≤ |w i * w j * (‖v i - v j‖ ^ 2 - a)| := le_abs_self _
          _ = |w i * w j| * |‖v i - v j‖ ^ 2 - a| := abs_mul _ _
          _ ≤ |w i * w j| * ε := mul_le_mul_of_nonneg_left (hdist i j hij) (abs_nonneg _)
      have htwo : 2 * |w i * w j| ≤ w i ^ 2 + w j ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
      have := mul_le_mul_of_nonneg_left htwo hε
      nlinarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpair i j))
  have hdiag : (∑ i, ∑ j, if i = j then a * w i ^ 2 else 0) = a * ∑ i, w i ^ 2 := by
    simp [← Finset.mul_sum]
  have hmain : (∑ i, ∑ j, a * w i * w j) = 0 := by
    simp only [← Finset.mul_sum, hw, mul_zero, Finset.sum_const_zero]
  have herror : (∑ i, ∑ j, ε / 2 * (w i ^ 2 + w j ^ 2)) =
      ε * (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.card_univ]
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at htotal
  rw [hzero, hmain, hdiag, herror] at htotal
  have hsnonneg : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs0 : (∑ i, w i ^ 2) = 0 := by nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    sq_nonneg (w j))).mp hs0 i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

theorem no_five_in_shell (v : Fin 5 → EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r)
    (hlow : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖)
    (hupp : ∀ i j, i ≠ j → ‖v i - v j‖ ≤ (1 + shellDelta) * r) : False := by
  have hai : AffineIndependent ℝ v := by
    apply affineIndependent_of_sq_dist_close v
      (a := r ^ 2) (ε := (2 * shellDelta + shellDelta ^ 2) * r ^ 2)
    · dsimp [shellDelta]
      positivity
    · simp only [Fintype.card_fin]
      dsimp [shellDelta]
      nlinarith [sq_pos_of_pos hr]
    · intro i j hij
      have hlo := hlow i j hij
      have hup := hupp i j hij
      rw [abs_le]
      constructor
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hr.le hnorm |>.mpr hlo
        dsimp [shellDelta]
        nlinarith [sq_nonneg r]
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hnorm (by dsimp [shellDelta]; positivity) |>.mpr hup
        dsimp [shellDelta] at hsq ⊢
        nlinarith
  have hdim := hai.card_le_finrank_succ
  have hle := Submodule.finrank_le (vectorSpan ℝ (range v))
  have hthree : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hthree] at hle
  simp only [Fintype.card_fin] at hdim
  omega

theorem shellGraph_cliqueFree {ι : Type u_1} (v : ι → EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) : (shellGraph v r).CliqueFree 5 := by
  classical
  intro s hs
  let e : ↥s ≃ Fin 5 := Finset.equivFinOfCardEq hs.card_eq
  let q : Fin 5 → EuclideanSpace ℝ (Fin 3) := fun i => v (e.symm i)
  apply no_five_in_shell q hr
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.1
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.2

theorem shellGraph_edge_bound {ι : Type u_1} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    letI := Classical.decRel (shellGraph v r).Adj
    8 * (shellGraph v r).edgeFinset.card ≤ 3 * (Fintype.card ι) ^ 2 := by
  classical
  have h := (shellGraph_cliqueFree v hr).card_edgeFinset_le (r := 4)
  simp only at h
  have hm : Fintype.card ι % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hle : (Fintype.card ι % 4) ^ 2 ≤ Fintype.card ι ^ 2 :=
    Nat.pow_le_pow_left (Nat.mod_le _ _) 2
  generalize Fintype.card ι % 4 = m at h hm hle
  generalize Fintype.card ι ^ 2 = N at h hle ⊢
  generalize (shellGraph v r).edgeFinset.card = E at h ⊢
  interval_cases m <;> simp at h hle ⊢ <;> omega

theorem coreProfile_ge_of_not_shell (t r : ℝ) (hr : r < 1)
    (hnot : ¬ (Real.exp (-t) ≤ r ∧ r ≤ (1 + shellDelta) * Real.exp (-t))) :
    t ^ 2 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs with hlow hhigh
  · have hp : 0 ≤ (Real.exp (-t) / r) ^ 12 := by positivity
    linarith
  · exact False.elim (hnot ⟨le_of_not_gt hlow, hhigh⟩)
  · rfl

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem two_mul_pairSum {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsym : ∀ i j, f i j = f j i) :
    2 * pairSum f = ∑ i, ∑ j, if i = j then 0 else f i j := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else f i j) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, hsym i j]
  simp_rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : ι => if j < i then f j i else 0)]
  simp only [pairSum, Finset.sum_filter]
  ring

theorem sum_adjacency_indicator {ι : Type u_1} [Fintype ι] (G : SimpleGraph ι) :
    letI := Classical.decRel G.Adj
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  have h := congrArg (fun n : ℕ => (n : ℝ)) G.two_mul_card_edgeFinset
  rw [Finset.card_filter] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite] at h
  rw [Fintype.sum_prod_type] at h
  simpa only [Nat.cast_one, Nat.cast_zero] using h.symm

theorem core_one_cell_bound {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (Fintype.card ι : ℝ) ^ 2 - t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let G := shellGraph v (Real.exp (-t))
  have hpoint (i j : ι) :
      t ^ 2 * (1 - (if G.Adj i j then 1 else 0) - (if i = j then 1 else 0)) ≤
        if i = j then 0 else coreProfile t ‖v i - v j‖ := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_right hij, sub_zero]
      by_cases hadj : G.Adj i j
      · simp only [ite_eq_left hadj, sub_self, mul_zero]
        exact coreProfile_nonneg _ _
      · simp only [ite_eq_right hadj, sub_zero, mul_one]
        apply coreProfile_ge_of_not_shell _ _ (hdiam i j)
        intro hshell
        exact hadj ⟨hij, hshell⟩
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint i j))
  have horient := two_mul_pairSum (fun i j => coreProfile t ‖v i - v j‖)
    (fun i j => by rw [norm_sub_rev])
  have hadj := sum_adjacency_indicator G
  have hdiag : (∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else 0) = Fintype.card ι := by simp
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at htotal
  rw [hadj, hdiag, ← horient] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hedge := shellGraph_edge_bound v (Real.exp_pos (-t))
  have hedger : 8 * (G.edgeFinset.card : ℝ) ≤ 3 * (Fintype.card ι : ℝ) ^ 2 := by exact_mod_cast hedge
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hedger)]

theorem row_sum_quadratic_bound {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, n i ^ 2 := by
  have hYoung (i j : ι) : 2 * (J i j * n i * n j) ≤
      J i j * n i ^ 2 + J i j * n j ^ 2 := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hYoung i j))
  simp_rw [Finset.sum_add_distrib] at hs
  simp only [← Finset.mul_sum] at hs
  have hswap : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsym j i]
  rw [hswap] at hs
  have hr : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem superstable_algebra {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M t N Ucore Uattr : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M)
    (hcore : t ^ 2 / 8 * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore)
    (hattr : Uattr ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * n i * n j) :
    (t ^ 2 / 8 - M / 2) * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore - Uattr := by
  have hq := row_sum_quadratic_bound J n M hJ hsym hrow
  nlinarith

theorem sum_subtype_le_of_nonneg {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i : {i // p i}, f i ≤ ∑ i, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hp : 0 ≤ ∑ i : {i // ¬ p i}, f i := Finset.sum_nonneg (fun i _ => hf i)
  linarith

theorem core_partition_bound {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, c i = c j → ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤ pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let f (i j : ι) : ℝ := if i = j then 0 else coreProfile t ‖v i - v j‖
  have hf (i j : ι) : 0 ≤ f i j := by
    dsimp [f]
    split_ifs
    · rfl
    · exact coreProfile_nonneg _ _
  let U (k : κ) : ℝ := pairSum (fun i j : {i // c i = k} => coreProfile t ‖v i - v j‖)
  have htwocell (k : κ) : 2 * U k = ∑ i : {i // c i = k}, ∑ j : {j // c j = k}, f i j := by
    dsimp [U]
    rw [two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])]
    simp only [f, Subtype.ext_iff]
  have htwototal : 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) = ∑ i, ∑ j, f i j :=
    two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])
  have hu : 2 * (∑ k, U k) ≤ 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
    rw [Finset.mul_sum, htwototal]
    simp_rw [htwocell]
    calc
      _ ≤ ∑ k : κ, ∑ i : {i // c i = k}, ∑ j : ι, f i j := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sum_subtype_le_of_nonneg (fun j => c j = k) (f i) (hf i)
      _ = _ := Fintype.sum_fiberwise c (fun i => ∑ j, f i j)
  have hs (k : κ) : t ^ 2 / 8 * (Fintype.card {i // c i = k} : ℝ) ^ 2 -
      t ^ 2 / 2 * Fintype.card {i // c i = k} ≤ U k := by
    apply core_one_cell_bound
    intro i j
    exact hdiam i j (i.property.trans j.property.symm)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) => hs k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hcard : (∑ k, (Fintype.card {i // c i = k} : ℝ)) = Fintype.card ι := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Fintype.sum_fiberwise c (fun _ => (1 : ℝ))
  rw [hcard] at hsum
  linarith

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LatticeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem dist_lt_one_of_cellIndex_eq {x y : EuclideanSpace ℝ (Fin 3)}
    (h : cellIndex x = cellIndex y) : ‖x - y‖ < 1 := by
  have hcoord (k : Fin 3) : |x k - y k| < (1 / 4 : ℝ) := by
    have heq : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxlo := Int.floor_le (4 * x k)
    have hxhi := Int.lt_floor_add_one (4 * x k)
    have hylo := Int.floor_le (4 * y k)
    have hyhi := Int.lt_floor_add_one (4 * y k)
    rw [heq] at hxlo hxhi
    rw [abs_lt]
    constructor <;> linarith
  have hsq (k : Fin 3) : (x k - y k) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have hc := (hcoord k).le
    have := sq_le_sq₀ (abs_nonneg (x k - y k)) (by norm_num : (0 : ℝ) ≤ 1 / 4) |>.mpr hc
    simpa only [sq_abs] using this
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hsq k)
  have hnorm : ‖x - y‖ ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using hsum
  nlinarith [norm_nonneg (x-y)]

theorem mem_nearCells_iff {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ ∀ k, |j k - i k| ≤ cellRadius R := by
  simp only [nearCells, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' (fun k => ?_)
  omega

theorem nearCells_symm {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ i ∈ nearCells R j := by
  simp only [mem_nearCells_iff, abs_sub_comm]

theorem cellRadius_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellRadius R :=
  Int.ceil_nonneg (by linarith)

theorem cellRadius_le {R : ℝ} (hR : 1 ≤ R) : (cellRadius R : ℝ) ≤ 6 * R := by
  have h := Int.ceil_lt_add_one (4 * R + 1)
  dsimp [cellRadius]
  linarith

theorem card_nearCells {R : ℝ} (hR : 0 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) = (2 * (cellRadius R : ℝ) + 1) ^ 3 := by
  have hn := cellRadius_nonneg hR
  have hc (k : Fin 3) : ((Finset.Icc (i k - cellRadius R) (i k + cellRadius R)).card : ℝ) =
      2 * (cellRadius R : ℝ) + 1 := by
    have h := Int.card_Icc_of_le (i k - cellRadius R) (i k + cellRadius R) (by omega)
    exact_mod_cast h.trans (by ring)
  rw [nearCells, Fintype.card_piFinset, Nat.cast_prod]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_nearCells_le {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  rw [card_nearCells (by linarith)]
  have hn := cellRadius_nonneg (show 0 ≤ R by linarith)
  have hn' : (0 : ℝ) ≤ cellRadius R := by exact_mod_cast hn
  have h : 2 * (cellRadius R : ℝ) + 1 ≤ 13 * R := by
    have := cellRadius_le hR
    linarith
  have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * cellRadius R + 1) h 3
  nlinarith only [hp]

theorem cellIndex_mem_nearCells {x y : EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hd : ‖x - y‖ ≤ R) : cellIndex y ∈ nearCells R (cellIndex x) := by
  rw [mem_nearCells_iff]
  intro k
  have hx1 := Int.floor_le (4 * x k)
  have hx2 := Int.lt_floor_add_one (4 * x k)
  have hy1 := Int.floor_le (4 * y k)
  have hy2 := Int.lt_floor_add_one (4 * y k)
  have hcoord : |x k - y k| ≤ R := by
    have h := PiLp.norm_apply_le (x - y) k
    have hc : |x k - y k| ≤ ‖x - y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h
    exact hc.trans hd
  have hceil : 4 * R + 1 ≤ (cellRadius R : ℝ) := Int.le_ceil _
  have habs : |((cellIndex y k : ℤ) : ℝ) - (cellIndex x k : ℝ)| ≤
      (cellRadius R : ℝ) := by
    dsimp [cellIndex]
    rw [abs_le] at hcoord ⊢
    constructor <;> linarith
  exact_mod_cast habs

theorem latticeEnvelope_nonneg {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    0 ≤ latticeEnvelope R i j := by
  unfold latticeEnvelope
  split_ifs <;> positivity

theorem latticeEnvelope_symm (R : ℝ) (i j : Lattice) :
    latticeEnvelope R i j = latticeEnvelope R j i := by
  simp only [latticeEnvelope, nearCells_symm (i := i) (j := j)]

theorem latticeEnvelope_le {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    latticeEnvelope R i j ≤ R⁻¹ ^ 3 := by
  unfold latticeEnvelope
  split_ifs
  · rfl
  · positivity

theorem sum_latticeEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ∑ j, latticeEnvelope R i (f j) ≤ 2197 := by
  classical
  let s := Finset.univ.filter (fun j : κ => f j ∈ nearCells R i)
  have hcard : s.card ≤ (nearCells R i).card :=
    Finset.card_le_card_of_injOn f (by
      intro j hj
      exact (Finset.mem_filter.mp hj).2) hf.injOn
  have hsum : (∑ j, latticeEnvelope R i (f j)) = (s.card : ℝ) * R⁻¹ ^ 3 := by
    simp only [latticeEnvelope, ← Finset.sum_filter, s, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ ((nearCells R i).card : ℝ) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (by positivity)
    _ ≤ (2197 * R ^ 3) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (card_nearCells_le hR i) (by positivity)
    _ = 2197 := by field_simp

theorem kernel_le_latticeEnvelope (w : ℝ → ℝ) (H R : ℝ)
    (hheight : ∀ r, w r ≤ R⁻¹ ^ 3 * H) (hsupport : ∀ r, R < r → w r = 0)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    w ‖x - y‖ ≤ H * latticeEnvelope R (cellIndex x) (cellIndex y) := by
  by_cases h : cellIndex y ∈ nearCells R (cellIndex x)
  · simpa only [latticeEnvelope, ite_eq_left h, mul_comm H] using hheight ‖x - y‖
  · have hd : R < ‖x - y‖ := lt_of_not_ge (fun hle => h (cellIndex_mem_nearCells hle))
    rw [hsupport _ hd, latticeEnvelope, ite_eq_right h, mul_zero]

theorem summable_mixedEnvelope_terms {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i j : Lattice) :
    Summable (fun n => σ n * latticeEnvelope (R n) i j) := by
  apply hs.of_norm_bounded
  intro n
  have hRp : 0 ≤ R n := le_trans zero_le_one (hR n)
  rw [Real.norm_of_nonneg (mul_nonneg (hσ n) (latticeEnvelope_nonneg hRp i j))]
  have he : latticeEnvelope (R n) i j ≤ 1 :=
    (latticeEnvelope_le hRp i j).trans
      (pow_le_one₀ (inv_nonneg.mpr hRp) (inv_le_one_of_one_le₀ (hR n)))
  simpa using mul_le_mul_of_nonneg_left he (hσ n)

theorem mixedEnvelope_nonneg {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 0 ≤ R n) (i j : Lattice) :
    0 ≤ mixedEnvelope σ R i j :=
  tsum_nonneg (fun n => mul_nonneg (hσ n) (latticeEnvelope_nonneg (hR n) i j))

theorem mixedEnvelope_symm (σ R : ℕ → ℝ) (i j : Lattice) :
    mixedEnvelope σ R i j = mixedEnvelope σ R j i := by
  unfold mixedEnvelope
  congr 1
  funext n
  rw [latticeEnvelope_symm]

theorem sum_mixedEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i : Lattice) :
    ∑ j, mixedEnvelope σ R i (f j) ≤ 2197 * ∑' n, σ n := by
  have hsum : Summable (fun n => ∑ j, σ n * latticeEnvelope (R n) i (f j)) := by
    apply Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hσ n) (latticeEnvelope_nonneg (le_trans zero_le_one (hR n)) i (f j)))) _
      (hs.mul_left 2197)
    intro n
    rw [← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
    nlinarith only [hh]
  unfold mixedEnvelope
  rw [← Summable.tsum_finsetSum (fun j _ => summable_mixedEnvelope_terms hσ hR hs i (f j)),
    ← hs.tsum_mul_left]
  apply hsum.tsum_le_tsum _ (hs.mul_left 2197)
  intro n
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
  nlinarith only [hh]

theorem attraction_le_mixedEnvelope {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (x y : Space) :
    attraction t σ R ‖x - y‖ ≤
      (t * kernelHeight) * mixedEnvelope σ R (cellIndex x) (cellIndex y) := by
  unfold attraction mixedEnvelope
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ht
  rw [← tsum_mul_left]
  apply (summable_attraction_terms hσ hR hs _).tsum_le_tsum _
    ((summable_mixedEnvelope_terms hσ hR hs _ _).mul_left kernelHeight)
  intro n
  have hh := kernel_le_latticeEnvelope (scaledKernelProfile (R n)) kernelHeight (R n)
    (fun r => by simpa only [kernelHeight, div_eq_mul_inv, one_mul] using
      scaledKernelProfile_le (lt_of_lt_of_le zero_lt_one (hR n)) r)
    (fun r hr => scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR n)) hr.le) x y
  have hh' := mul_le_mul_of_nonneg_left hh (hσ n)
  nlinarith only [hh']

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem sum_comp_eq_sum_fibres {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (c : ι → κ) (f : κ → ℝ) :
    (∑ i, f (c i)) = ∑ k, (Fintype.card {i // c i = k} : ℝ) * f k := by
  symm
  calc
    _ = ∑ k, ∑ _i : {i // c i = k}, f k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ k, ∑ i : {i // c i = k}, f (c i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ = _ := Fintype.sum_fiberwise c (fun i => f (c i))

theorem pairSum_le_cell_quadratic {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (J : κ → κ → ℝ) (F : ι → ι → ℝ)
    (hJ : ∀ k l, 0 ≤ J k l) (hsym : ∀ i j, F i j = F j i)
    (hF : ∀ i j, F i j ≤ J (c i) (c j)) :
    pairSum F ≤ (1 / 2 : ℝ) * ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
  classical
  have hh (i j : ι) : (if i = j then 0 else F i j) ≤ J (c i) (c j) := by
    split_ifs
    · exact hJ _ _
    · exact hF _ _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hh i j))
  rw [← two_mul_pairSum F hsym] at hs
  have hsum : (∑ i, ∑ j, J (c i) (c j)) = ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
    calc
      _ = ∑ i, ∑ l, (Fintype.card {j // c j = l} : ℝ) * J (c i) l := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_comp_eq_sum_fibres c (fun l => J (c i) l)
      _ = ∑ k, (Fintype.card {i // c i = k} : ℝ) *
          (∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l) :=
        sum_comp_eq_sum_fibres c (fun k => ∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hsum] at hs
  linarith

theorem physicalProfile_pairSum_lower {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    {ι : Type u_1} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    -(t ^ 2 / 2) * Fintype.card ι ≤ pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let s := Finset.univ.image (fun i : ι => cellIndex (x i))
  let c (i : ι) : s := ⟨cellIndex (x i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let J (k l : s) := (t * kernelHeight) * mixedEnvelope σ R k l
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : s) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) k l)
  have hJsym (k l : s) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : s) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left
      (sum_mixedEnvelope_le (fun l : s => (l : Lattice)) Subtype.val_injective hσ hR hs k)
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => attraction_le_mixedEnvelope ht hσ hR hs _ _)
  have hb := superstable_algebra J (fun k : s => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  have hn : 0 ≤ ∑ k : s, (Fintype.card {i // c i = k} : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm : 0 ≤ t ^ 2 / 8 - M / 2 := sub_nonneg.mpr hsmall
  have hp := mul_nonneg hm hn
  have heq : pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) =
      pairSum (fun i j => coreProfile t ‖x i - x j‖) -
      pairSum (fun i j => attraction t σ R ‖x i - x j‖) := by
    simp only [pairSum, physicalProfile, Finset.sum_sub_distrib]
  rw [heq]
  linarith

theorem ereal_coe_sum {ι : Type u_1} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simpa only [Finset.sum_insert hi, EReal.coe_add] using congrArg (fun z => (f i : EReal) + z) ih

theorem coe_pairSum_le_energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    ((pairSum (fun i j => φ ‖x i - x j‖) : ℝ) : EReal) ≤ energy φ x := by
  classical
  simp only [pairSum, energy, ereal_coe_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold radialPotential
  split_ifs
  · exact le_top
  · rfl

theorem physicalProfile_stable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) :
    ((-(t ^ 2 / 2) * (N : ℝ) : ℝ) : EReal) ≤ energy (physicalProfile t σ R) x := by
  apply le_trans _ (coe_pairSum_le_energy _ x)
  apply EReal.coe_le_coe_iff.mpr
  simpa only [Fintype.card_fin] using physicalProfile_pairSum_lower ht hσ hR hs hsmall x

theorem physicalProfile_superstable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    (t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let J (k l : κ) := (t * kernelHeight) * mixedEnvelope σ R (e k) (e l)
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : κ) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) (e k) (e l))
  have hJsym (k l : κ) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : κ) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left (sum_mixedEnvelope_le e he hσ hR hs (e k))
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq ((hc i).trans ((congrArg e hij).trans (hc j).symm)))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => by
      have hh := attraction_le_mixedEnvelope ht hσ hR hs (x i) (x j)
      simpa only [hc, J] using hh)
  have hb := superstable_algebra J (fun k : κ => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  simpa only [pairSum, physicalProfile, Finset.sum_sub_distrib] using hb

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CubeCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem cellIndex_mem_cubeCells {L : ℝ} {x : Space} (hx : x ∈ cube L) :
    cellIndex x ∈ cubeCells L := by
  classical
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellIndex]
  intro k
  constructor
  · apply Int.floor_mono
    have h := (hx k).1
    linarith
  · apply Int.floor_mono
    have h := (hx k).2
    linarith

theorem card_cubeCells_le {L : ℝ} (hL : 0 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ (4 * L + 2) ^ 3 := by
  classical
  let m := (Finset.Icc ⌊-2 * L⌋ ⌊2 * L⌋).card
  have horder : ⌊-2 * L⌋ ≤ ⌊2 * L⌋ + 1 := by
    have hh := Int.floor_mono (show -2 * L ≤ 2 * L by linarith)
    omega
  have hcInt := Int.card_Icc_of_le ⌊-2 * L⌋ ⌊2 * L⌋ horder
  have hcReal : (m : ℝ) = (⌊2 * L⌋ : ℝ) + 1 - (⌊-2 * L⌋ : ℝ) := by
    dsimp only [m]
    exact_mod_cast hcInt
  have hm : (m : ℝ) ≤ 4 * L + 2 := by
    rw [hcReal]
    have hu := Int.floor_le (2 * L)
    have hl := Int.lt_floor_add_one (-2 * L)
    linarith
  have hc : ((cubeCells L).card : ℝ) = (m : ℝ) ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, m]
  rw [hc]
  exact pow_le_pow_left₀ (Nat.cast_nonneg m) hm 3

theorem physicalProfile_energy_coercive {t L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) (hx : ∀ i, x i ∈ cube L) :
    (((t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      ((N : ℝ) ^ 2 / (4 * L + 2) ^ 3) - t ^ 2 / 2 * N : ℝ) : EReal) ≤
      energy (physicalProfile t σ R) x := by
  classical
  let κ := (cubeCells L : Type)
  let c (i : Fin N) : κ := ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  let n (k : κ) : ℝ := Fintype.card {i // c i = k}
  have hsN : (∑ k : κ, n k) = N := by
    have hh := sum_comp_eq_sum_fibres c (fun _ => (1 : ℝ))
    simpa only [n, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using hh.symm
  have hquad : (N : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, n k ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun _ => (1 : ℝ)) n
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hsN] using hh
  have hquad' : (N : ℝ) ^ 2 ≤ (4 * L + 2) ^ 3 * ∑ k, n k ^ 2 := by
    apply hquad.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    simpa only [κ, Fintype.card_coe] using card_cubeCells_le hL
  have hden : 0 < (4 * L + 2) ^ 3 := by positivity
  have hquot : (N : ℝ) ^ 2 / (4 * L + 2) ^ 3 ≤ ∑ k, n k ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hquad'
  have hsuper := physicalProfile_superstable ht hσ hR hs x c
    (fun k : κ => (k : Lattice)) Subtype.val_injective (fun _ => rfl)
  have he := coe_pairSum_le_energy (physicalProfile t σ R) x
  apply le_trans _ he
  apply EReal.coe_le_coe_iff.mpr
  have hm := mul_le_mul_of_nonneg_left hquot (sub_nonneg.mpr hsmall)
  simp only [Fintype.card_fin] at hsuper
  exact (sub_le_sub_right hm _).trans hsuper

end

end ContinuumTemperature

end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

theorem ereal_sum_ne_bot {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
    exact ⟨hf i (Finset.mem_insert_self i s), ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))⟩

theorem measurable_energy {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (N : ℕ) : Measurable (fun x : Fin N → Space => energy φ x) := by
  classical
  unfold energy
  fun_prop

theorem measurable_boltzmann {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (β : ℝ) (N : ℕ) : Measurable (fun x : Fin N → Space => boltzmann φ β x) := by
  have hE := measurable_energy hφ N
  exact Measurable.ite (hE (measurableSet_singleton ⊤)) measurable_const
    ((measurable_const.mul hE.ereal_toReal).exp)

theorem boltzmann_nonneg (φ : ℝ → ℝ) (β : ℝ) {N : ℕ} (x : Fin N → Space) :
    0 ≤ boltzmann φ β x := by
  unfold boltzmann
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem boltzmann_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ≤ Real.exp (β * B * N) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal (hstable N x) (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    nlinarith [mul_le_mul_of_nonneg_left he hβ]

theorem isCompact_cube (L : ℝ) : IsCompact (cube L) := by
  have h := isCompact_pi_infinite (fun _ : Fin 3 => isCompact_Icc (a := -L / 2) (b := L / 2))
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr h

theorem isCompact_configurations (L : ℝ) (N : ℕ) :
    IsCompact {x : Fin N → Space | ∀ i, x i ∈ cube L} :=
  isCompact_pi_infinite (fun _ => isCompact_cube L)

theorem integrableOn_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) :
    IntegrableOn (fun x : Fin N → Space => boltzmann φ β x)
      {x : Fin N → Space | ∀ i, x i ∈ cube L} := by
  have hK := isCompact_configurations L N
  have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  apply (integrable_const (Real.exp (β * B * N))).mono'
    (measurable_boltzmann hφ β N).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ β x)]
  exact boltzmann_le_of_stable hβ hstable x

theorem energy_eq_real_of_injective (φ : ℝ → ℝ) {N : ℕ} {x : Fin N → Space}
    (hx : Function.Injective x) :
    energy φ x = ((∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      φ ‖x i - x j‖ : ℝ) : EReal) := by
  classical
  unfold energy
  simp only [ereal_coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  exact ite_eq_right (sub_ne_zero.mpr (hx.ne hij))

theorem boltzmann_pos_of_injective (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    {x : Fin N → Space} (hx : Function.Injective x) : 0 < boltzmann φ β x := by
  unfold boltzmann
  rw [ite_eq_right (by rw [energy_eq_real_of_injective φ hx]; exact EReal.coe_ne_top _)]
  exact Real.exp_pos _

theorem isOpen_openConfigurations (L : ℝ) (N : ℕ) :
    IsOpen (openConfigurations L N) := by
  have hbox : IsOpen {x : Fin N → Space | ∀ i k, x i k ∈ Ioo (-L / 2) (L / 2)} := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_Ioo.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp
      (continuous_apply i))
  have hinj : IsOpen {x : Fin N → Space | Function.Injective x} := by
    have heq : {x : Fin N → Space | Function.Injective x} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | x i ≠ x j} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h i j hij => h.ne hij, fun h i j hij => by_contra fun hij' => h i j hij' hij⟩
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl
  exact hbox.inter hinj

theorem openConfigurations_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (openConfigurations L N).Nonempty := by
  let c : ℝ := L / (4 * ((N : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  let x : Fin N → Space := fun i => WithLp.toLp 2 (fun _ : Fin 3 => (i : ℝ) * c)
  refine ⟨x, ?_, ?_⟩
  · intro i k
    change -L / 2 < (i : ℝ) * c ∧ (i : ℝ) * c < L / 2
    have hi : (i : ℝ) < N := by exact_mod_cast i.isLt
    have hinonneg : 0 ≤ (i : ℝ) := by positivity
    constructor
    · nlinarith [mul_nonneg hinonneg hc.le]
    · dsimp [c]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hL (by exact_mod_cast Nat.zero_lt_succ N : 0 < (N : ℝ) + 1)]
  · intro i j he
    have hij := congrArg (fun y : Space => y 0) he
    change (i : ℝ) * c = (j : ℝ) * c at hij
    have hij' := mul_right_cancel₀ hc.ne' hij
    exact Fin.ext (by exact_mod_cast hij')

theorem partition_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : 0 < partition φ β L N := by
  classical
  unfold partition
  split_ifs
  · norm_num
  · apply mul_pos (by positivity)
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
    apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
      (openConfigurations_nonempty hL N))
    apply measure_mono
    intro x hx
    exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
      fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem boltzmann_add (φ : ℝ → ℝ) (β γ : ℝ) {N : ℕ} (x : Fin N → Space) :
    boltzmann φ (β + γ) x = boltzmann φ β x * boltzmann φ γ x := by
  unfold boltzmann
  split_ifs
  · ring
  · rw [← Real.exp_add]
    congr 1
    ring

theorem boltzmann_rpow (φ : ℝ → ℝ) (β : ℝ) {p : ℝ} (hp : 0 < p)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ^ p = boltzmann φ (p * β) x := by
  unfold boltzmann
  split_ifs
  · exact Real.zero_rpow hp.ne'
  · rw [← Real.exp_mul]
    congr 1
    ring

theorem integral_boltzmann_logconvex {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B : ℝ}
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) {β γ a b : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ (a * β + b * γ) x) ≤
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b := by
  let μ : Measure (Fin N → Space) :=
    volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hp (c u : ℝ) (hc : 0 < c) (x : Fin N → Space) :
      ‖boltzmann φ (c * u) x‖ ^ (1 / c) = boltzmann φ u x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (c * u) x),
      boltzmann_rpow φ (c * u) (one_div_pos.mpr hc)]
    congr 1
    field_simp
  have hLp (c u : ℝ) (hc : 0 < c) (hu : 0 < u) :
      MemLp (fun x : Fin N → Space => boltzmann φ (c * u) x) (ENNReal.ofReal (1 / c)) μ := by
    have A : ENNReal.ofReal (1 / c) ≠ 0 := by positivity
    have B' : ENNReal.ofReal (1 / c) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← memLp_norm_rpow_iff _ A B', ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / c),
      ENNReal.div_self A B', memLp_one_iff_integrable]
    · apply (integrableOn_boltzmann hφ hu.le hstable L N).congr
      exact ae_of_all _ (fun x => (hp c u hc x).symm)
    · exact (measurable_boltzmann hφ (c * u) N).aestronglyMeasurable
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (ae_of_all μ (boltzmann_nonneg φ (a * β)))
    (ae_of_all μ (boltzmann_nonneg φ (b * γ)))
    (hLp a β ha hβ) (hLp b γ hb hγ)
  simp only [one_div_one_div] at hHolder
  convert hHolder using 1
  · exact integral_congr_ae (ae_of_all μ (boltzmann_add φ (a * β) (b * γ)))
  · congr 2
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (a * β) x)]
        using (hp a β ha x).symm
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (b * γ) x)]
        using (hp b γ hb x).symm

theorem integral_boltzmann_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) :
    0 < ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
  apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
    (openConfigurations_nonempty hL N))
  apply measure_mono
  intro x hx
  exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
    fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem convexOn_log_integral_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x)) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  simp only [smul_eq_mul]
  have hβ' := integral_boltzmann_pos hφ hβ.le hL hstable N
  have hγ' := integral_boltzmann_pos hφ hγ.le hL hstable N
  have hac : 0 < a * β + b * γ := add_pos (mul_pos ha hβ) (mul_pos hb hγ)
  have hc := integral_boltzmann_pos hφ hac.le hL hstable N
  have hHolder := integral_boltzmann_logconvex hφ hstable L N hβ hγ ha hb hab
  calc
    _ ≤ Real.log ((∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b) :=
      Real.log_le_log hc hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos hβ' a).ne' (Real.rpow_pos_of_pos hγ' b).ne',
      Real.log_rpow hβ', Real.log_rpow hγ']

theorem convexOn_log_partition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log (partition φ β L N)) := by
  by_cases hN : N = 0
  · simp only [hN, partition, ↓reduceIte, Real.log_one]
    exact convexOn_const _ (convex_Ioi _)
  · have hlog (β : ℝ) (hβ : 0 < β) : Real.log (partition φ β L N) =
        Real.log (1 / (N.factorial : ℝ)) + Real.log
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) := by
      unfold partition
      rw [ite_eq_right hN, Real.log_mul (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)))
        (integral_boltzmann_pos hφ hβ.le hL hstable N).ne']
    have hc := convexOn_log_integral_boltzmann hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro β hβ γ hγ a b ha hb hab
    simp only [smul_eq_mul]
    rw [hlog _ (add_pos (mul_pos ha hβ) (mul_pos hb hγ)), hlog β hβ, hlog γ hγ]
    have hi := hc.2 hβ hγ ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    have hcst : a * Real.log (1 / (N.factorial : ℝ)) +
        b * Real.log (1 / (N.factorial : ℝ)) = Real.log (1 / (N.factorial : ℝ)) := by
      rw [← add_mul, hab, one_mul]
    nlinarith only [hi, hcst]

theorem volume_cube (L : ℝ) : volume (cube L) = (ENNReal.ofReal L) ^ 3 := by
  have heq : cube L = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin 3 => Icc (-L / 2) (L / 2))) := by
    ext x
    simp only [cube, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet)]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) _ = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Icc]
  have ha : L / 2 - -L / 2 = L := by ring
  simp [ha]

theorem volume_configurations (L : ℝ) (N : ℕ) :
    volume {x : Fin N → Space | ∀ i, x i ∈ cube L} = (ENNReal.ofReal L) ^ (3 * N) := by
  have heq : {x : Fin N → Space | ∀ i, x i ∈ cube L} =
      Set.pi Set.univ (fun _ : Fin N => cube L) := by ext x; simp
  rw [heq]
  change (Measure.pi (fun _ : Fin N => (volume : Measure Space))) _ = _
  rw [Measure.pi_pi]
  simp only [volume_cube, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem partition_nonneg (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    0 ≤ partition φ β L N := by
  unfold partition
  split_ifs
  · norm_num
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (boltzmann_nonneg φ β)

theorem partition_le_exp_of_stable {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    partition φ β L N ≤ (L ^ 3 * Real.exp (β * B)) ^ N / (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN, partition]
  · have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
    have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
      (integrable_const (Real.exp (β * B * N)))
      (ae_of_all _ (boltzmann_le_of_stable hβ hstable (N := N)))
    rw [integral_const] at hi
    simp only [Measure.real, Measure.restrict_apply_univ, volume_configurations,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hL, smul_eq_mul] at hi
    unfold partition
    rw [ite_eq_right hN]
    have hfac : 0 ≤ (1 / (N.factorial : ℝ)) := by positivity
    apply (mul_le_mul_of_nonneg_left hi hfac).trans_eq
    rw [show β * B * (N : ℝ) = (N : ℝ) * (β * B) by ring, Real.exp_nat_mul,
      mul_pow, pow_mul]
    ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem summable_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ β L N) := by
  apply Summable.of_nonneg_of_le (fun N => mul_nonneg (Real.exp_pos _).le
    (partition_nonneg φ β L N)) _
    (Real.summable_pow_div_factorial (Real.exp (t * h) * (L ^ 3 * Real.exp (β * B))))
  intro N
  have hb := mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos (t * h * N)).le
  apply hb.trans_eq
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul, mul_pow]
  ring

theorem grandPartition_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    grandPartition φ t β h L ≤ Real.exp (L ^ 3 * Real.exp (t * h + β * B)) := by
  let z := L ^ 3 * Real.exp (t * h + β * B)
  have hz : HasSum (fun N : ℕ => z ^ N / (N.factorial : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  unfold grandPartition
  rw [← hz.tsum_eq]
  apply (summable_grandPartition hφ hβ hL hstable t h).tsum_le_tsum _ hz.summable
  intro N
  apply (mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos _).le).trans_eq
  dsimp [z]
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul,
    Real.exp_add, mul_pow, mul_pow]
  ring

theorem tsum_logconvex_bound {f g k : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hk : Summable k)
    (hfS : Summable f) (hgS : Summable g) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hbound : ∀ n, k n ≤ f n ^ a * g n ^ b) :
    (∑' n, k n) ≤ (∑' n, f n) ^ a * (∑' n, g n) ^ b := by
  have heq (x c : ℝ) (hx : 0 ≤ x) (hc : 0 < c) : (x ^ c) ^ (1 / c) = x := by
    rw [← Real.rpow_mul hx, mul_one_div_cancel hc.ne', Real.rpow_one]
  have hu : Summable (fun n => (f n ^ a) ^ (1 / a)) := by
    simpa only [heq _ a (hf _) ha] using hfS
  have hv : Summable (fun n => (g n ^ b) ^ (1 / b)) := by
    simpa only [heq _ b (hg _) hb] using hgS
  obtain ⟨hS, hH⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (fun n => Real.rpow_nonneg (hf n) a) (fun n => Real.rpow_nonneg (hg n) b) hu hv
  simp only [heq _ a (hf _) ha, heq _ b (hg _) hb, one_div_one_div] at hH
  exact (hk.tsum_le_tsum hbound hS).trans hH

theorem convexOn_log_tsum {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (F : ℕ → E → ℝ)
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (hconv : ∀ n, ConvexOn ℝ s (fun x => Real.log (F n x)))
    (hS : ∀ x, x ∈ s → Summable (fun n => F n x)) :
    ConvexOn ℝ s (fun x => Real.log (∑' n, F n x)) := by
  have hp (x : E) (hx : x ∈ s) : 0 < ∑' n, F n x :=
    (hpos 0 x hx).trans_le ((hS x hx).le_tsum 0 (fun n _ => (hpos n x hx).le))
  refine convexOn_iff_forall_pos.mpr ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hs hx hy ha.le hb.le hab
  have hbnd (n : ℕ) : F n (a • x + b • y) ≤ F n x ^ a * F n y ^ b := by
    have hc := (hconv n).2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hc
    apply (Real.log_le_log_iff (hpos n _ hz) (mul_pos
      (Real.rpow_pos_of_pos (hpos n x hx) a) (Real.rpow_pos_of_pos (hpos n y hy) b))).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos (hpos n x hx) a).ne'
      (Real.rpow_pos_of_pos (hpos n y hy) b).ne', Real.log_rpow (hpos n x hx),
      Real.log_rpow (hpos n y hy)]
    exact hc
  have hHolder := tsum_logconvex_bound (fun n => (hpos n x hx).le)
    (fun n => (hpos n y hy).le) (hS _ hz) (hS x hx) (hS y hy) ha hb hab hbnd
  calc
    _ ≤ Real.log ((∑' n, F n x) ^ a * (∑' n, F n y) ^ b) :=
      Real.log_le_log (hp _ hz) hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos (hp x hx) a).ne'
      (Real.rpow_pos_of_pos (hp y hy) b).ne',
      Real.log_rpow (hp x hx), Real.log_rpow (hp y hy)]; rfl

theorem convexOn_log_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t : ℝ) :
    ConvexOn ℝ {x : ℝ × ℝ | 0 < x.1}
      (fun x => Real.log (grandPartition φ t x.1 x.2 L)) := by
  have hdomain : Convex ℝ {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.1 + b * y.1
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by simpa using hab
      simpa [hb'] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
  apply convexOn_log_tsum hdomain
    (fun N x => Real.exp (t * x.2 * N) * partition φ x.1 L N)
  · intro N x hx
    exact mul_pos (Real.exp_pos _) (partition_pos hφ hx.le hL hstable N)
  · intro N
    have hc := convexOn_log_partition hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨hdomain, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz := hdomain hx hy ha.le hb.le hab
    have log_eq (z : ℝ × ℝ) (hz : 0 < z.1) :
        Real.log (Real.exp (t * z.2 * N) * partition φ z.1 L N) =
          t * z.2 * N + Real.log (partition φ z.1 L N) := by
      rw [Real.log_mul (Real.exp_pos _).ne'
        (partition_pos hφ hz.le hL hstable N).ne', Real.log_exp]
    rw [log_eq _ hz, log_eq _ hx, log_eq _ hy]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have hi := hc.2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    nlinarith only [hi]
  · intro x hx
    exact summable_grandPartition hφ hx.le hL.le hstable t x.2

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FiniteBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_factorial_lower (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hpos.le N
    have hl := Real.log_le_log (div_pos (pow_pos hpos _) hf) hh
    rw [Real.log_div (pow_ne_zero _ hpos.ne') hf.ne', Real.log_pow, Real.log_exp] at hl
    linarith

theorem boltzmann_le_of_energy_lower {φ : ℝ → ℝ} {β E : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} {x : Fin N → Space} (hE : (E : EReal) ≤ energy φ x) :
    boltzmann φ β x ≤ Real.exp (-β * E) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal hE (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    exact mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hβ)

theorem partition_le_factorial_of_energy_bound {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    partition φ β L N ≤ (L ^ 3) ^ N / (N.factorial : ℝ) * Real.exp (-β * E) := by
  let S := {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hS : MeasurableSet S := (isCompact_configurations L N).measurableSet
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
  have hh : ∀ᵐ x ∂volume.restrict S, boltzmann φ β x ≤ Real.exp (-β * E) := by
    apply (ae_restrict_iff' hS).mpr
    exact ae_of_all _ (fun x hx => boltzmann_le_of_energy_lower hβ (hE x hx))
  have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
    (integrable_const (Real.exp (-β * E))) hh
  have hc : (∫ x in S, Real.exp (-β * E)) = L ^ (3 * N) * Real.exp (-β * E) := by
    rw [setIntegral_const, Measure.real, volume_configurations, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hL, smul_eq_mul]
  rw [hc] at hi
  unfold partition
  rw [ite_eq_right hN]
  calc
    _ ≤ (1 / (N.factorial : ℝ)) * (L ^ (3 * N) * Real.exp (-β * E)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [pow_mul]; ring

theorem neg_log_partition_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    β * E + N * Real.log ((N : ℝ) / L ^ 3) - N ≤ -Real.log (partition φ β L N) := by
  have hnpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hfp : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hLp : 0 < L ^ 3 := pow_pos hL _
  have hZ := partition_pos hφ hβ hL hstable N
  have hu := partition_le_factorial_of_energy_bound hφ hβ hL.le hstable hN hE
  have hl := Real.log_le_log hZ hu
  rw [Real.log_mul (div_pos (pow_pos hLp _) hfp).ne' (Real.exp_pos _).ne',
    Real.log_div (pow_pos hLp _).ne' hfp.ne', Real.log_pow, Real.log_exp] at hl
  rw [Real.log_div hnpos.ne' hLp.ne']
  have hf := log_factorial_lower N
  nlinarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem ereal_sum_eq_top_of_exists {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) (ht : ∃ i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ht
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨j, hj, hjt⟩ := ht
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hjt]
      exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot s f
        (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    · rw [ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) ⟨j, hj, hjt⟩]
      exact EReal.add_top_of_ne_bot (hf i (Finset.mem_insert_self _ _))

theorem energy_eq_top_iff (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    energy φ x = ⊤ ↔ ¬Function.Injective x := by
  constructor
  · intro he hx
    rw [energy_eq_real_of_injective φ hx] at he
    exact EReal.coe_ne_top _ he
  · intro hx
    have hh : ∃ i j, i ≠ j ∧ x i = x j := by
      by_contra hc
      apply hx
      intro i j heq
      by_contra hne
      exact hc ⟨i, j, hne, heq⟩
    obtain ⟨i, j, hij, he⟩ := hh
    have hpair {i j : Fin N} (hij : i < j) (he : x i = x j) : energy φ x = ⊤ := by
      apply ereal_sum_eq_top_of_exists _ _
        (fun i _ => ereal_sum_ne_bot _ _ (fun j _ => radialPotential_ne_bot _ _))
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply ereal_sum_eq_top_of_exists _ _ (fun j _ => radialPotential_ne_bot _ _)
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, by
        simp [he, radialPotential]⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair h he
    · exact hpair h he.symm

theorem realPairEnergy_eq_ordered (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (x : ι → Space) :
    realPairEnergy φ x = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), φ ‖x i - x j‖ := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else φ ‖x i - x j‖) =
      (if i < j then φ ‖x i - x j‖ else 0) +
      (if j < i then φ ‖x j - x i‖ else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, norm_sub_rev]
  calc
    realPairEnergy φ x = (1/2 : ℝ) * ∑ i, ∑ j,
        ((if i < j then φ ‖x i - x j‖ else 0) +
          (if j < i then φ ‖x j - x i‖ else 0)) := by
      unfold realPairEnergy
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using hsplit i j
      · simpa only [ite_eq_right hij] using hsplit i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : ι => if j < i then φ ‖x j - x i‖ else 0)]
      simp only [Finset.sum_filter]
      ring

theorem boltzmann_eq_symmetricWeight (φ : ℝ → ℝ) (β : ℝ)
    {N : ℕ} (x : Fin N → Space) : boltzmann φ β x = symmetricWeight φ β x := by
  classical
  by_cases hx : Function.Injective x
  · simp only [boltzmann, energy_eq_real_of_injective φ hx, EReal.coe_ne_top,
      ite_false, EReal.toReal_coe, symmetricWeight, ite_eq_left hx, realPairEnergy_eq_ordered]
  · simp only [boltzmann, (energy_eq_top_iff φ x).2 hx, ite_true, symmetricWeight, ite_eq_right hx]

theorem realPairEnergy_relabel (φ : ℝ → ℝ) {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : realPairEnergy φ (x ∘ e) = realPairEnergy φ x := by
  classical
  unfold realPairEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else φ ‖x (e i) - x j‖)

theorem symmetricWeight_relabel (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} {κ : Type u_2}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Space) :
    symmetricWeight φ β (x ∘ e) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x :=
    by
      constructor
      · intro hx i j hij
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        exact congrArg e (hx hij)
      · exact fun hx => hx.comp e.injective
  simp only [symmetricWeight, hh, realPairEnergy_relabel]

theorem symmetric_matrix_split {ι : Type u_1} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (F : ι → ι → ℝ) (hsym : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      (∑ i : {i // p i}, ∑ j : {j // p j}, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : {j // ¬p j}, F i j) +
      2 * (∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j) := by
  classical
  have houter := Fintype.sum_subtype_add_sum_subtype p (fun i => ∑ j, F i j)
  have hinner (i : ι) := Fintype.sum_subtype_add_sum_subtype p (F i)
  rw [← houter]
  simp_rw [← hinner, Finset.sum_add_distrib]
  have hh : (∑ i : {i // ¬p i}, ∑ j : {j // p j}, F i j) =
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsym _ _
  rw [hh]
  ring

theorem realPairEnergy_split (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    realPairEnergy φ x =
      realPairEnergy φ (fun i : {i // p i} => x i) +
      realPairEnergy φ (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖ := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else φ ‖x i - x j‖)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm, norm_sub_rev])
  have hcross (i : {i // p i}) (j : {i // ¬p i}) : (i : ι) ≠ j := by
    intro h
    exact j.property (h ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold realPairEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem symmetricWeight_nonneg (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) : 0 ≤ symmetricWeight φ β x := by
  unfold symmetricWeight
  split_ifs
  · positivity
  · rfl

theorem symmetricWeight_separated (φ : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type u_1} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {A B : Set Space} (hd : Disjoint A B)
    (hφ : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (x : ι → Space) (hA : ∀ i, p i → x i ∈ A) (hB : ∀ i, ¬p i → x i ∈ B) :
    symmetricWeight φ β (fun i : {i // p i} => x i) *
      symmetricWeight φ β (fun i : {i // ¬p i} => x i) ≤ symmetricWeight φ β x := by
  classical
  by_cases ha : Function.Injective (fun i : {i // p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right ha, zero_mul] using symmetricWeight_nonneg φ β x
  by_cases hb : Function.Injective (fun i : {i // ¬p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right hb, mul_zero] using symmetricWeight_nonneg φ β x
  have hx : Function.Injective x := by
    intro i j hij
    by_cases hi : p i <;> by_cases hj : p j
    · exact congrArg Subtype.val (ha (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
    · exact False.elim (Set.disjoint_left.mp hd (hA i hi) (hij ▸ hB j hj))
    · exact False.elim (Set.disjoint_left.mp hd (hA j hj) (hij ▸ hB i hi))
    · exact congrArg Subtype.val (hb (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
  have hc : (∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact Finset.sum_nonpos (fun j _ => hφ _ (hA i i.property) _ (hB j j.property))
  simp only [symmetricWeight, ite_eq_left ha, ite_eq_left hb, ite_eq_left hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [realPairEnergy_split φ p x]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hc]

theorem realPairEnergy_translate (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    realPairEnergy φ (fun i => x i + v) = realPairEnergy φ x := by
  classical
  simp only [realPairEnergy, add_sub_add_right_eq_sub]

theorem symmetricWeight_translate (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    symmetricWeight φ β (fun i => x i + v) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (fun i => x i + v) ↔ Function.Injective x := by
    simp only [Function.Injective, add_left_inj]
  simp only [symmetricWeight, hh, realPairEnergy_translate]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Assignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section Assignments
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem measurableSet_assignmentRegion {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (e : Equiv.Perm ι) : MeasurableSet (assignmentRegion B e) := by
  convert MeasurableSet.iInter (fun i => (hB (e i)).preimage (measurable_pi_apply i)) using 1
  ext x
  simp [assignmentRegion]

omit [MeasurableSpace X] in
theorem assignmentRegion_pairwiseDisjoint {B : ι → Set X}
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Pairwise (fun e f : Equiv.Perm ι => Disjoint (assignmentRegion B e) (assignmentRegion B f)) := by
  intro e f hef
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hne : ∃ i, e i ≠ f i := by
    by_contra! h
    exact hef (Equiv.ext h)
  obtain ⟨i, hi⟩ := hne
  exact Set.disjoint_left.mp (hB hi) (hx i) (hy i)

theorem measure_assignment_union (μ : Measure X) [SigmaFinite μ] {B : ι → Set X}
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (Measure.pi (fun _ : ι => μ)) (⋃ e : Equiv.Perm ι, assignmentRegion B e) =
      (Fintype.card ι).factorial * ∏ i, μ (B i) := by
  rw [measure_iUnion (assignmentRegion_pairwiseDisjoint hd)
    (measurableSet_assignmentRegion hB), tsum_fintype]
  have hh (e : Equiv.Perm ι) :
      (Measure.pi (fun _ : ι => μ)) (assignmentRegion B e) = ∏ i, μ (B i) := by
    have heq : assignmentRegion B e = Set.univ.pi (fun i => B (e i)) := by
      ext x
      simp [assignmentRegion]
    rw [heq, Measure.pi_pi, Equiv.prod_comp e (fun i => μ (B i))]
  simp_rw [hh]
  simp [Fintype.card_perm]

theorem integral_lower_of_disjoint_assignments (μ : Measure X) [SigmaFinite μ]
    {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hfinite : ∀ i, μ (B i) ≠ ⊤) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x) {c : ℝ}
    (hinc : ∀ e, assignmentRegion B e ⊆ Ω)
    (hbound : ∀ e, ∀ x ∈ assignmentRegion B e, c ≤ F x) :
    (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let S := ⋃ e : Equiv.Perm ι, assignmentRegion B e
  have hS : MeasurableSet S := MeasurableSet.iUnion (measurableSet_assignmentRegion hB)
  have hsub : S ⊆ Ω := iUnion_subset hinc
  have hmass := measure_assignment_union μ hB hd
  have hSfin : (Measure.pi (fun _ : ι => μ)) S ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.prod_ne_top (fun i _ => hfinite i))
  have hconst : IntegrableOn (fun _ : ι → X => c) S (Measure.pi (fun _ : ι => μ)) :=
    integrableOn_const hSfin
  have hle : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
    apply setIntegral_mono_on hconst (hF.mono_set hsub) hS
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    exact hbound e x he
  have hle' := setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)
  have hval : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c := by
    rw [setIntegral_const, Measure.real, hmass, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_prod, smul_eq_mul]
  rw [hval] at hle
  exact hle.trans hle'

omit [DecidableEq ι] in

theorem setIntegral_coordinatePerm (μ : Measure X) [SigmaFinite μ]
    (e : Equiv.Perm ι) (S : Set (ι → X)) (F : (ι → X) → ℝ)
    (hsym : ∀ x, F (x ∘ e) = F x) :
    (∫ x in {x | (x ∘ e) ∈ S}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let p : (ι → X) ≃ᵐ (ι → X) := MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm
  have hpx (x : ι → X) : p x = x ∘ e := by
    ext i
    simpa only [p, Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => X) x (e i))
  have hp : MeasurePreserving p (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun _ : ι => μ)) := measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding F S
  simpa only [hpx, hsym, Set.preimage] using heq

theorem measurableSet_binaryRegion {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (s : Finset ι) : MeasurableSet (binaryRegion A B s) := by
  have hh (i : ι) : MeasurableSet ((fun x : ι → X => x i) ⁻¹' (if i ∈ s then A else B)) := by
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using hA.preimage (measurable_pi_apply i)
    · simpa only [ite_eq_right hi] using hB.preimage (measurable_pi_apply i)
  convert MeasurableSet.iInter hh using 1
  ext x
  simp only [binaryRegion, mem_ofPred_eq, mem_iInter, mem_preimage]
  apply forall_congr'
  intro i
  split_ifs <;> rfl

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_pairwiseDisjoint {A B : Set X} (hd : Disjoint A B) :
    Pairwise (fun s t : Finset ι => Disjoint (binaryRegion A B s) (binaryRegion A B t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hst
  ext i
  constructor
  · intro hi
    by_contra ht
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hx i)
      (by simpa only [ite_eq_right ht] using hy i)
  · intro hi
    by_contra hs
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hy i)
      (by simpa only [ite_eq_right hs] using hx i)

theorem setIntegral_binaryRegion_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} {s t : Finset ι} (hst : s.card = t.card) (F : (ι → X) → ℝ)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x) :
    (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  have hmem (i : ι) : e i ∈ t ↔ i ∈ s := by
    rw [← he]
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact e.injective hji ▸ hj
    · exact fun hi => ⟨i, hi, rfl⟩
  have hpre : {x : ι → X | (x ∘ e) ∈ binaryRegion A B s} = binaryRegion A B t := by
    ext x
    change (∀ i, if i ∈ s then x (e i) ∈ A else x (e i) ∈ B) ↔
      (∀ i, if i ∈ t then x i ∈ A else x i ∈ B)
    simp_rw [← hmem]
    constructor
    · intro hh j
      obtain ⟨i, rfl⟩ := e.surjective j
      exact hh i
    · intro hh i
      exact hh (e i)
  have hh := setIntegral_coordinatePerm μ e (binaryRegion A B s) F (hsym e)
  rw [hpre] at hh
  exact hh.symm

theorem integral_lower_binary_assignments (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω) :
    (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  classical
  let T := (Finset.univ : Finset ι).powersetCard s.card
  have hcard (t : Finset ι) (ht : t ∈ T) : t.card = s.card := (Finset.mem_powersetCard.mp ht).2
  have hsub : (⋃ t ∈ T, binaryRegion A B t) ⊆ Ω := by
    intro x hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
    exact hinc t (hcard t ht) hx
  have hh := integral_biUnion_finset T (fun t _ => measurableSet_binaryRegion hA hB t)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun t ht => hF.mono_set (hinc t (hcard t ht)))
  have hEq : (∫ x in ⋃ t ∈ T, binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) := by
    rw [hh]
    calc
      _ = ∑ _t ∈ T, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact setIntegral_binaryRegion_eq μ (hcard t ht) F hsym
      _ = _ := by simp [T]
  rw [← hEq]
  exact setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)

theorem setIntegral_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    (f : ({i : ι // i ∈ s} → X) → ℝ) (g : ({i : ι // i ∉ s} → X) → ℝ) :
    (∫ x in binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i)
      ∂(Measure.pi (fun _ : ι => μ))) =
    (∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
    (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
      ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding
    (fun z => f z.1 * g z.2) (SA ×ˢ SB)
  rw [hpre, setIntegral_prod_mul] at heq
  exact heq

theorem integrableOn_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) :
    IntegrableOn (fun x : ι → X =>
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i))
      (binaryRegion A B s) (Measure.pi (fun _ : ι => μ)) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have hprod : IntegrableOn (fun z => f z.1 * g z.2) (SA ×ˢ SB)
      ((Measure.pi (fun _ : {i : ι // i ∈ s} => μ)).prod
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hf.mul_prod hg
  have hh := (hp.integrableOn_comp_preimage p.measurableEmbedding).2 hprod
  rw [hpre] at hh
  exact hh

theorem integral_lower_separated_product (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))
    (hbound : ∀ x ∈ binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i) ≤ F x) :
    (Fintype.card ι).choose s.card *
      ((∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
      (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
        ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hle := setIntegral_mono_on (integrableOn_binary_product μ A B s hf hg)
    (hF.mono_set (hinc s rfl)) (measurableSet_binaryRegion hA hB s) hbound
  rw [setIntegral_binary_product] at hle
  exact (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)).trans
    (integral_lower_binary_assignments μ hA hB hd s hF hF0 hsym hinc)

omit [MeasurableSpace X] [Fintype ι] [DecidableEq ι] in

theorem binomial_factorial_cancel {n k : ℕ} (hk : k ≤ n) {a b I : ℝ}
    (h : (n.choose k : ℝ) * (a * b) ≤ I) :
    (a / (k.factorial : ℝ)) * (b / ((n-k).factorial : ℝ)) ≤ I / (n.factorial : ℝ) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (le_div_iff₀ hn).2
  rw [Nat.cast_choose ℝ hk] at h
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end Assignments

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section GeneralLabels
variable {ι : Type u_1} [Fintype ι]

theorem measurable_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) (β : ℝ) :
    Measurable (fun x : ι → Space => symmetricWeight φ β x) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hm : Measurable (fun x : ι → Space => x ∘ e) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (e i)
  have hh := (measurable_boltzmann hφ β (Fintype.card ι)).comp hm
  change Measurable (fun x => boltzmann φ β (x ∘ e)) at hh
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem symmetricWeight_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (x : ι → Space) :
    symmetricWeight φ β x ≤ Real.exp (β * B * Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hh := boltzmann_le_of_stable hβ hstable (x ∘ e)
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem integrableOn_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {Ω : Set (ι → Space)} (hΩ : volume Ω ≠ ⊤) :
    IntegrableOn (fun x : ι → Space => symmetricWeight φ β x) Ω := by
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hΩ⟩
  apply (integrable_const (Real.exp (β * B * Fintype.card ι))).mono'
    (measurable_symmetricWeight hφ β).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (symmetricWeight_nonneg φ β x)]
  exact symmetricWeight_le_of_stable hβ hstable x

theorem generalPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    0 ≤ generalPartition φ β A ι := by
  apply div_nonneg
  · apply integral_nonneg
    exact symmetricWeight_nonneg φ β
  · positivity

theorem generalPartition_eq_partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    generalPartition φ β (cube L) (Fin N) = partition φ β L N := by
  classical
  by_cases hN : N = 0
  · subst N
    have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
    have hv : volume.real (Set.univ : Set (Fin 0 → Space)) = 1 := by
      simp [Measure.real, volume_pi]
    simp [generalPartition, partition, symmetricWeight, realPairEnergy, hinj, hv]
  · simp only [generalPartition, partition, hN, ite_false, Fintype.card_fin,
      ← boltzmann_eq_symmetricWeight, div_eq_mul_inv, one_mul]
    ring

theorem volume_generalConfigurations (A : Set Space) :
    volume {x : ι → Space | ∀ i, x i ∈ A} = (volume A) ^ Fintype.card ι := by
  have heq : {x : ι → Space | ∀ i, x i ∈ A} = Set.univ.pi (fun _ : ι => A) := by
    ext x
    simp
  rw [heq, volume_pi_pi]
  simp

theorem generalPartition_binary_lower [DecidableEq ι] {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (s : Finset ι) :
    generalPartition φ β A {i : ι // i ∈ s} *
      generalPartition φ β B {i : ι // i ∉ s} ≤ generalPartition φ β C ι := by
  classical
  have hΩ : volume {x : ι → Space | ∀ i, x i ∈ C} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hC
  have hmA : volume A ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono haC)
  have hmB : volume B ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hbC)
  have hΩA : volume {x : {i : ι // i ∈ s} → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmA
  have hΩB : volume {x : {i : ι // i ∉ s} → Space | ∀ i, x i ∈ B} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmB
  have hInt := integral_lower_separated_product volume hA hB hd s
    (integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (symmetricWeight_relabel φ β)
    (fun t _ x hx i => by
      by_cases hi : i ∈ t
      · exact haC (by simpa only [ite_eq_left hi] using hx i)
      · exact hbC (by simpa only [ite_eq_right hi] using hx i))
    (integrableOn_symmetricWeight hφ hβ hstable hΩA)
    (integrableOn_symmetricWeight hφ hβ hstable hΩB)
    (fun x hx => by
      have hh := symmetricWeight_separated φ hβ (fun i => i ∈ s) hd hcross x
        (fun i hi => by simpa only [ite_eq_left hi] using hx i)
        (fun i hi => by simpa only [ite_eq_right hi] using hx i)
      have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
        Subsingleton.elim _ _
      rw [hfi] at hh
      exact hh)
  have hh := binomial_factorial_cancel (Finset.card_le_univ s) hInt
  simpa only [generalPartition, Fintype.card_subtype_compl,
    Fintype.card_coe, volume_pi] using hh

end GeneralLabels

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TrialConfigurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable section

theorem trialBall_coord {q : ℝ} {i : Lattice} {x : Space} (hx : x ∈ trialBall q i)
    (k : Fin 3) : |x k - q * (i k : ℝ)| < q / 8 := by
  have hh := PiLp.norm_apply_le (x - gridPoint q i) k
  have hd : ‖x - gridPoint q i‖ < q / 8 := by
    simpa only [trialBall, Metric.mem_ball, dist_eq_norm] using hx
  have hc : |x k - q * (i k : ℝ)| ≤ ‖x - gridPoint q i‖ := by
    simpa [gridPoint] using hh
  exact hc.trans_lt hd

theorem trialBall_separation {q : ℝ} (hq : 0 < q) {i j : Lattice} (hij : i ≠ j)
    {x y : Space} (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) :
    3 * q / 4 < ‖x - y‖ := by
  obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := by
    by_contra! h
    exact hij (funext h)
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hc : |x k - y k| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  rw [abs_lt] at hxk hyk
  rw [abs_le] at hc
  rcases lt_or_gt_of_ne hk with h | h
  · have hh : (i k : ℝ) + 1 ≤ (j k : ℝ) := by exact_mod_cast h
    nlinarith
  · have hh : (j k : ℝ) + 1 ≤ (i k : ℝ) := by exact_mod_cast h
    nlinarith

theorem trialBall_disjoint {q : ℝ} (hq : 0 < q) :
    Pairwise (fun i j : Lattice => Disjoint (trialBall q i) (trialBall q j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hh := trialBall_separation hq hij hi hj
  simp only [sub_self, norm_zero] at hh
  linarith

theorem mem_gridNeighbors_iff {q : ℝ} {i j : Lattice} :
    j ∈ gridNeighbors q i ↔ ∀ k, |j k - i k| ≤ gridRadius q := by
  simp only [gridNeighbors, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem trialBall_close_mem {q : ℝ} (hq : 0 < q) {i j : Lattice} {x y : Space}
    (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) (hxy : ‖x-y‖ < 1) :
    j ∈ gridNeighbors q i := by
  rw [mem_gridNeighbors_iff]
  intro k
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hn : |x k - y k| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  have hc : |x k - y k| < 1 := hn.trans_lt hxy
  have hceil : q⁻¹ + 1 ≤ (gridRadius q : ℝ) := Int.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hq.le
  have hcancel : q * (q⁻¹ + 1) = 1 + q := by field_simp
  rw [hcancel] at hmul
  have hh : |((j k : ℤ) : ℝ) - (i k : ℝ)| ≤ (gridRadius q : ℝ) := by
    rw [abs_lt] at hxk hyk hc
    rw [abs_le]
    constructor <;> nlinarith
  exact_mod_cast hh

theorem gridRadius_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ gridRadius q := by
  exact Int.ceil_nonneg (by positivity)

theorem card_gridNeighbors {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (gridNeighbors q i).card = (2 * (gridRadius q).toNat + 1) ^ 3 := by
  have hr := gridRadius_nonneg hq
  simp only [gridNeighbors, Fintype.card_piFinset, Int.card_Icc]
  have hh (k : Fin 3) : (i k + gridRadius q + 1 - (i k - gridRadius q)).toNat =
      2 * (gridRadius q).toNat + 1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem grid_close_card_le {ι : Type u_1} [Fintype ι] {q : ℝ} (hq : 0 < q)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℕ) ≤
      (2 * (gridRadius q).toNat + 1)^3 := by
  classical
  rw [← card_gridNeighbors hq (f i)]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    exact trialBall_close_mem hq (hx i) (hx j) (Finset.mem_filter.mp hj).2
  · exact hf.injOn

theorem trialEnergyConstant_nonneg (t q : ℝ) : 0 ≤ trialEnergyConstant t q := by
  unfold trialEnergyConstant
  positivity

theorem trial_core_row_le {ι : Type u_1} [Fintype ι] [DecidableEq ι] {q t : ℝ} (hq : 0 < q) (ht : 1 < t)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖) ≤ trialEnergyConstant t q := by
  classical
  let C := t^2 + (Real.exp (-t) / (3*q/4))^12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖)) ≤
      ∑ j, (if ‖x i-x j‖ < 1 then C else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
      split_ifs <;> positivity
    · rw [ite_eq_right hij]
      by_cases hdist : ‖x i-x j‖ < 1
      · rw [ite_eq_left hdist]
        exact coreProfile_le (by linarith : 0 < 3*q/4)
          (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j)).le t
      · rw [ite_eq_right hdist, coreProfile_eq_zero ht (le_of_not_gt hdist)]
  have hh := grid_close_card_le hq f hf x hx i
  have hcard : ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) ≤
      (2 * (gridRadius q).toNat + 1 : ℝ)^3 := by exact_mod_cast hh
  calc
    _ ≤ _ := hsum
    _ = ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) * C := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (2 * (gridRadius q).toNat + 1 : ℝ)^3 * C := mul_le_mul_of_nonneg_right hcard hC
    _ = trialEnergyConstant t q := rfl

theorem interiorGrid_ball_subset {q L : ℝ} (hq : 0 < q) (hL : 2*q ≤ L)
    {i : Lattice} (hi : i ∈ interiorGrid q L) : trialBall q i ⊆ cube L := by
  intro x hx k
  have hk : -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
    have hh : ∀ k, -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
      simpa only [interiorGrid, Fintype.mem_piFinset, Finset.mem_Icc] using hi
    exact hh k
  have hk1 : -(⌊L/(2*q)-1⌋₊ : ℝ) ≤ (i k : ℝ) := by exact_mod_cast hk.1
  have hk2 : (i k : ℝ) ≤ (⌊L/(2*q)-1⌋₊ : ℝ) := by exact_mod_cast hk.2
  have hnonneg : 0 ≤ L/(2*q)-1 := by
    have : 1 ≤ L/(2*q) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    linarith
  have hn := Nat.floor_le hnonneg
  have heq : (L/(2*q)-1)*(2*q) = L-2*q := by field_simp
  have hmul := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 2*q)
  rw [heq] at hmul
  have hxk := trialBall_coord hx k
  rw [abs_lt] at hxk
  constructor <;> nlinarith

theorem card_interiorGrid (q L : ℝ) :
    (interiorGrid q L).card = (2*⌊L/(2*q)-1⌋₊+1)^3 := by
  simp only [interiorGrid, Fintype.card_piFinset, Int.card_Icc]
  have hh : ((⌊L/(2*q)-1⌋₊ : ℤ) + 1 - -(⌊L/(2*q)-1⌋₊ : ℤ)).toNat =
      2*⌊L/(2*q)-1⌋₊+1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_interiorGrid_lower {q L : ℝ} (hq : 0 < q) (hL : 8*q ≤ L) :
    (L/(2*q))^3 ≤ ((interiorGrid q L).card : ℝ) := by
  rw [card_interiorGrid]
  push_cast
  have hh := Nat.lt_floor_add_one (L/(2*q)-1)
  have heq : (L/(2*q))*(2*q) = L := by field_simp
  have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < 2*q)
  have hL0 : 0 ≤ L := by linarith
  have hden : 0 ≤ L/(2*q) := div_nonneg hL0 (by positivity)
  have hle : L/(2*q) ≤ 2*(⌊L/(2*q)-1⌋₊ : ℝ)+1 := by nlinarith
  exact pow_le_pow_left₀ hden hle 3

theorem exists_trial_sites {q L D : ℝ} (hq : 0 < q) (hL : 8*q ≤ L)
    (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    ∃ f : Fin N → Lattice, Function.Injective f ∧
      ∀ i, trialBall q (f i) ⊆ cube L := by
  have hL0 : 0 ≤ L := by linarith
  have hc : (N : ℝ) ≤ ((interiorGrid q L).card : ℝ) := calc
    _ ≤ D*L^3 := hN
    _ ≤ (2*q)⁻¹ ^ 3 * L^3 := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (L/(2*q))^3 := by ring
    _ ≤ _ := card_interiorGrid_lower hq hL
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (interiorGrid q L) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (show N ≤ (interiorGrid q L).card by exact_mod_cast hc)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  exact interiorGrid_ball_subset hq (by linarith) (e i).property

theorem trialVolume_pos {q : ℝ} (hq : 0 < q) : 0 < trialVolume q := by
  unfold trialVolume
  positivity

theorem real_volume_trialBall {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (volume (trialBall q i)).toReal = trialVolume q := by
  simp only [trialBall, EuclideanSpace.volume_ball_fin_three, trialVolume,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ q/8),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]

theorem symmetricWeight_grid_lower {ι : Type u_1} [Fintype ι] {q t β : ℝ}
    (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β) {φ : ℝ → ℝ}
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) :
    Real.exp (-β * (trialEnergyConstant t q * Fintype.card ι)) ≤ symmetricWeight φ β x := by
  classical
  have hdist (i j : ι) (hij : i ≠ j) : 0 < ‖x i-x j‖ :=
    lt_trans (by linarith) (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j))
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hh := hdist i j hne
    simp only [hij, sub_self, norm_zero, lt_self_iff_false] at hh
  have hrow (i : ι) : (∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤ trialEnergyConstant t q := by
    apply le_trans _ (trial_core_row_le hq ht f hf x hx i)
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij, le_refl]
    · simp only [ite_eq_right hij]
      exact hcore _ (hdist i j hij)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  have hsum' : (∑ i, ∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤
      trialEnergyConstant t q * (Fintype.card ι : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum
  have hpos : 0 ≤ trialEnergyConstant t q * (Fintype.card ι : ℝ) :=
    mul_nonneg (trialEnergyConstant_nonneg t q) (Nat.cast_nonneg _)
  have he : realPairEnergy φ x ≤ trialEnergyConstant t q * Fintype.card ι := by
    unfold realPairEnergy
    nlinarith only [hsum', hpos]
  rw [symmetricWeight, ite_eq_left hinj]
  apply Real.exp_le_exp.mpr
  nlinarith only [he, hβ]

theorem partition_grid_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    {N : ℕ} (f : Fin N → Lattice) (hf : Function.Injective f)
    (hinc : ∀ i, trialBall q (f i) ⊆ cube L) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  classical
  let Bs := fun i : Fin N => trialBall q (f i)
  have hm : ∀ i, MeasurableSet (Bs i) := fun _ => measurableSet_ball
  have hd : Pairwise (fun i j => Disjoint (Bs i) (Bs j)) :=
    fun _ _ hij => trialBall_disjoint hq (fun h => hij (hf h))
  have hfin : ∀ i, volume (Bs i) ≠ ⊤ := fun _ => measure_ball_ne_top
  have hΩ : volume {x : Fin N → Space | ∀ i, x i ∈ cube L} ≠ ⊤ := by
    exact (isCompact_configurations L N).measure_lt_top.ne
  have hi := integral_lower_of_disjoint_assignments volume hm hd hfin
    (show IntegrableOn (fun x : Fin N → Space => symmetricWeight φ β x)
      {x | ∀ i, x i ∈ cube L} (Measure.pi fun _ => volume) by
      simpa only [← volume_pi] using integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (fun e x hx i => hinc (e i) (hx i))
    (fun e x hx => symmetricWeight_grid_lower hq ht hβ hcore (f ∘ e)
      (hf.comp e.injective) x hx)
  have hv : (∏ i : Fin N, (volume (Bs i)).toReal) = trialVolume q ^ N := by
    simp only [Bs, real_volume_trialBall hq, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hv, Fintype.card_fin] at hi
  have hn : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [← generalPartition_eq_partition, generalPartition, Fintype.card_fin]
  apply (le_div_iff₀ hn).2
  simpa only [mul_comm, mul_assoc, mul_left_comm, volume_pi] using hi

theorem partition_trial_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  obtain ⟨f, hf, hinc⟩ := exists_trial_sites hq hL hD hN
  exact partition_grid_lower hφ hq ht hβ hstable hcore f hf hinc

end

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.SpatialProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem generalPartition_relabel {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (e : ι ≃ κ) :
    generalPartition φ β A ι = generalPartition φ β A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (e i)
    · intro h i
      exact h (e.symm i)
  rw [hpre] at heq
  simp only [hpx, symmetricWeight_relabel] at heq
  unfold generalPartition
  rw [Fintype.card_congr e, heq]

theorem generalPartition_eq_setPartition {ι : Type u_1} [Fintype ι]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    generalPartition φ β A ι = setPartition φ β A (Fintype.card ι) :=
  generalPartition_relabel φ β A (Fintype.equivFin ι)

theorem setPartition_zero (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    setPartition φ β A 0 = 1 := by
  have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
  simp [setPartition, generalPartition, symmetricWeight, realPairEnergy, hinj,
    Measure.real, volume_pi]

theorem setPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) :
    0 ≤ setPartition φ β A N := generalPartition_nonneg φ β A

theorem setPartition_translate (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) (a : Space) :
    setPartition φ β ((fun x => x+a) '' A) N = setPartition φ β A N := by
  let p : (Fin N → Space) ≃ᵐ (Fin N → Space) := MeasurableEquiv.addRight (fun _ => a)
  have hp : MeasurePreserving p volume volume := measurePreserving_add_right volume (fun _ => a)
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A}
  have hpre : p ⁻¹' {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A} =
      {x : Fin N → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    apply forall_congr'
    intro i
    change x i + a ∈ (fun y => y+a) '' A ↔ x i ∈ A
    simp only [mem_image, add_left_inj, exists_eq_right]
  have hsym (x : Fin N → Space) : symmetricWeight φ β (p x) = symmetricWeight φ β x :=
    symmetricWeight_translate φ β x a
  rw [hpre] at heq
  simp only [hsym] at heq
  simpa only [setPartition, generalPartition, Fintype.card_fin] using
    congrArg (fun z : ℝ => z / (N.factorial : ℝ)) heq.symm

theorem setPartition_binary_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a-b‖ ≤ 0) (n m : ℕ) :
    setPartition φ β A n * setPartition φ β B m ≤ setPartition φ β C (n+m) := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin (n+m))).card by simp)
  have hh := generalPartition_binary_lower hφ hβ hstable hA hB hC hd haC hbC hcross s
  simpa only [generalPartition_eq_setPartition, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_fin, hs, Nat.add_sub_cancel_left] using hh

theorem setPartition_product_lower {κ : Type u_1} {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (A : κ → Set Space) (n : κ → ℕ) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, φ ‖a-b‖ ≤ 0)
    {C : Set Space} (hC : volume C ≠ ⊤) (hinc : ∀ i ∈ s, A i ⊆ C) :
    (∏ i ∈ s, setPartition φ β (A i) (n i)) ≤ setPartition φ β C (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simp [setPartition_zero]
  | @insert i s hi ih =>
    let U := ⋃ j ∈ s, A j
    have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable (fun j hj =>
      hA j (Finset.mem_insert_of_mem hj))
    have hUC : U ⊆ C := iUnion₂_subset (fun j hj => hinc j (Finset.mem_insert_of_mem hj))
    have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hUC)
    have hsub : ∀ j ∈ s, A j ⊆ U := fun j hj => subset_iUnion₂_of_subset j hj Subset.rfl
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hUf hsub
    have hdis : Disjoint (A i) U := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have henergy : ∀ a ∈ A i, ∀ b ∈ U, φ ‖a-b‖ ≤ 0 := by
      intro a ha b hb
      obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
      exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj)) a ha b hjb
    have hbin := setPartition_binary_lower hφ hβ hstable
      (hA i (Finset.mem_insert_self _ _)) hU hC hdis
      (hinc i (Finset.mem_insert_self _ _)) hUC henergy (n i) (∑ j ∈ s, n j)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_of_nonneg_left ih' (setPartition_nonneg φ β (A i) (n i))).trans hbin

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BoxTiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem isCompact_tileBox (ℓ L : ℝ) {k : ℕ} (i : Fin 3 → Fin k) :
    IsCompact (tileBox ℓ L i) :=
  (isCompact_cube ℓ).image (continuous_id.add continuous_const)

theorem tileBox_subset {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ)
    (hk : (k : ℝ)*(ℓ+2) ≤ L) (i : Fin 3 → Fin k) : tileBox ℓ L i ⊆ cube L := by
  rintro x ⟨y, hy, rfl⟩ j
  have hyj := hy j
  have hij : (i j : ℝ)+1 ≤ k := by exact_mod_cast (i j).isLt
  have h0 : (0 : ℝ) ≤ (i j : ℝ) := Nat.cast_nonneg _
  change y j + ((ℓ+2)*((i j : ℝ)+1/2)-L/2) ∈ Icc (-L/2) (L/2)
  constructor <;> nlinarith [hyj.1, hyj.2]

theorem tileBox_separation {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ)
    {i j : Fin 3 → Fin k} (hij : i ≠ j) {x y : Space}
    (hx : x ∈ tileBox ℓ L i) (hy : y ∈ tileBox ℓ L j) : 2 ≤ ‖x-y‖ := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨r, hr⟩ : ∃ r, i r ≠ j r := by
    by_contra! h
    exact hij (funext h)
  have har := ha r
  have hbr := hb r
  have hnorm : |(a+tileCenter ℓ L i) r - (b+tileCenter ℓ L j) r| ≤
      ‖(a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)) r
  change |a r + ((ℓ+2)*((i r : ℝ)+1/2)-L/2) -
    (b r + ((ℓ+2)*((j r : ℝ)+1/2)-L/2))| ≤
      ‖(a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)‖ at hnorm
  rw [abs_le] at hnorm
  rcases lt_or_gt_of_ne hr with h | h
  · have hh : (i r : ℝ)+1 ≤ (j r : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ ℓ+2)
    nlinarith [har.1, har.2, hbr.1, hbr.2]
  · have hh : (j r : ℝ)+1 ≤ (i r : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ ℓ+2)
    nlinarith [har.1, har.2, hbr.1, hbr.2]

theorem tileBox_pairwiseDisjoint {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ) :
    Pairwise (fun i j : Fin 3 → Fin k => Disjoint (tileBox ℓ L i) (tileBox ℓ L j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := tileBox_separation hℓ hij hx hy
  simp only [sub_self, norm_zero] at hh
  norm_num at hh

theorem partition_tiling_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B ℓ L : ℝ} (hβ : 0 ≤ β) (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0)
    (n : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) → ℕ) :
    (∏ i, partition φ β ℓ (n i)) ≤ partition φ β L (∑ i, n i) := by
  classical
  have hden : 0 < ℓ+2 := by linarith
  have hk : (⌊L/(ℓ+2)⌋₊ : ℝ)*(ℓ+2) ≤ L := by
    apply (le_div_iff₀ hden).mp
    exact Nat.floor_le (div_nonneg hL hden.le)
  have hh := setPartition_product_lower hφ hβ hstable (tileBox ℓ L) n Finset.univ
    (fun i _ => (isCompact_tileBox ℓ L i).measurableSet)
    (fun i _ j _ hij => tileBox_pairwiseDisjoint hℓ hij)
    (fun i _ j _ hij a ha b hb => hsign _ (le_trans (by norm_num)
      (tileBox_separation hℓ hij ha hb)))
    (isCompact_cube L).measure_lt_top.ne (fun i _ => tileBox_subset hℓ hk i)
  have hv (i : Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) :
      setPartition φ β (tileBox ℓ L i) (n i) = partition φ β ℓ (n i) := by
    rw [tileBox, setPartition_translate, setPartition, generalPartition_eq_partition]
  simp_rw [hv] at hh
  simpa only [setPartition, generalPartition_eq_partition] using hh

theorem exists_concentrated_counts (K H N : ℕ) (hN : N ≤ K*H) :
    ∃ r : Fin K → ℕ, (∑ i, r i) = N ∧ (∀ i, r i ≤ H) ∧
      (∑ i, if r i = 0 then 0 else 1) * H ≤ N+H := by
  induction K generalizing N with
  | zero =>
    have hzero : N = 0 := by omega
    subst N
    exact ⟨Fin.elim0, by simp, (fun i => Fin.elim0 i), by simp⟩
  | succ K ih =>
    by_cases hh : N ≤ H
    · refine ⟨Fin.cons N (fun _ => 0), ?_, ?_, ?_⟩
      · simp [Fin.sum_univ_succ]
      · intro i
        refine Fin.cases hh (fun _ => Nat.zero_le _) i
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_true, Finset.sum_const_zero,
          add_zero]
        split_ifs <;> omega
    · have hHK : N-H ≤ K*H := by
        rw [Nat.succ_mul] at hN
        omega
      obtain ⟨r, hr, hbound, hc⟩ := ih (N-H) hHK
      have hH : 0 < H := by
        by_contra hzero
        have hz : H = 0 := by omega
        simp only [hz, Nat.mul_zero, Nat.le_zero] at hN
        omega
      refine ⟨Fin.cons H r, ?_, ?_, ?_⟩
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hr]
        omega
      · intro i
        exact Fin.cases (le_refl H) hbound i
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_eq_right hH.ne']
        have hsub := Nat.sub_add_cancel (show H ≤ N by omega)
        nlinarith

theorem exists_adjusted_counts (K b H N : ℕ) (hb : 0 < b) (hH : 2*b ≤ H)
    (hN : N ≤ K*H) :
    ∃ r : Fin K → ℕ, (∑ i, r i) = N ∧ (∀ i, r i ≤ H) ∧
      ((∑ i, if r i = b then 0 else 1 : ℕ) : ℝ) * b ≤
        |(N : ℝ) - (K : ℝ)*b| + H := by
  have hbH : b ≤ H := by omega
  by_cases hNb : K*b ≤ N
  · have hdel : N-K*b ≤ K*(H-b) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    obtain ⟨d, hsum, hbound, hc⟩ := exists_concentrated_counts K (H-b) (N-K*b) hdel
    refine ⟨fun i => b+d i, ?_, ?_, ?_⟩
    · simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, hsum]
      omega
    · intro i
      change b+d i ≤ H
      have hh := hbound i
      omega
    · have heq : (∑ i, if b+d i = b then 0 else 1 : ℕ) =
          ∑ i, if d i = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.add_eq_left]
      rw [heq]
      have hineq : (∑ i, if d i = 0 then 0 else 1) * b ≤ (N-K*b)+H := by
        have hh := Nat.mul_le_mul_left (∑ i, if d i = 0 then 0 else 1) (show b ≤ H-b by omega)
        omega
      have hsub : ((N-K*b : ℕ) : ℝ) = (N : ℝ)-(K : ℝ)*b := by
        rw [Nat.cast_sub hNb, Nat.cast_mul]
      have hsgn : 0 ≤ (N : ℝ)-(K : ℝ)*b := by
        have hh : (K : ℝ)*b ≤ (N : ℝ) := by exact_mod_cast hNb
        linarith
      rw [abs_of_nonneg hsgn]
      have hh : ((∑ i, if d i = 0 then 0 else 1 : ℕ) : ℝ)*b ≤ ((N-K*b : ℕ) : ℝ)+H := by
        exact_mod_cast hineq
      rwa [hsub] at hh
  · have hNb' : N ≤ K*b := by omega
    obtain ⟨d, hsum, hbound, hc⟩ := exists_concentrated_counts K b (K*b-N) (Nat.sub_le _ _)
    refine ⟨fun i => b-d i, ?_, ?_, ?_⟩
    · have hh : (∑ i : Fin K, (b - d i)) + (∑ i : Fin K, d i) = K*b := by
        rw [← Finset.sum_add_distrib]
        simp only [Nat.sub_add_cancel (hbound _), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      change (∑ i : Fin K, (b - d i)) = N
      rw [hsum] at hh
      omega
    · intro i
      exact (Nat.sub_le b _).trans hbH
    · have heq : (∑ i, if b-d i = b then 0 else 1 : ℕ) =
          ∑ i, if d i = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hh : b-d i = b ↔ d i = 0 := by omega
        simp only [hh]
      rw [heq]
      have hineq : (∑ i, if d i = 0 then 0 else 1) * b ≤ (K*b-N)+H := by omega
      have hsub : ((K*b-N : ℕ) : ℝ) = (K : ℝ)*b-N := by
        rw [Nat.cast_sub hNb', Nat.cast_mul]
      have hsgn : (N : ℝ)-(K : ℝ)*b ≤ 0 := by
        have hh : (N : ℝ) ≤ (K : ℝ)*b := by exact_mod_cast hNb'
        linarith
      rw [abs_of_nonpos hsgn]
      have hh : ((∑ i, if d i = 0 then 0 else 1 : ℕ) : ℝ)*b ≤ ((K*b-N : ℕ) : ℝ)+H := by
        exact_mod_cast hineq
      rw [hsub] at hh
      linarith

theorem sum_baseline_le {K b H : ℕ} {r : Fin K → ℕ} {a : ℕ → ℝ} {M : ℝ}
    (hr : ∀ i, r i ≤ H) (ha : ∀ n, n ≤ H → a n ≤ M) (hb : -M ≤ a b) :
    ∑ i, a (r i) ≤ K*a b + 2*M*(∑ i, if r i = b then 0 else 1 : ℕ) := by
  classical
  calc
    ∑ i, a (r i) ≤ ∑ i, (a b + 2*M*(if r i = b then 0 else 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hh : r i = b
      · simp [hh]
      · simp only [ite_eq_right hh, Nat.cast_one, mul_one]
        linarith [ha (r i) (hr i)]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_sum]

theorem adjusted_box_comparison (a : ℝ → ℕ → ℝ) {ℓ L M : ℝ} {b H N : ℕ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hN : N ≤ tileCount ℓ L * H)
    (hbox : ∀ r : Fin (tileCount ℓ L) → ℕ, (∑ i, r i) = N →
      a L N ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i))
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    a L N ≤ ((tileCount ℓ L : ℝ)/L^3)*ℓ^3*a ℓ b +
      (2*M*ℓ^3/(b : ℝ)) * (|(N : ℝ)/L^3 - ((tileCount ℓ L : ℝ)/L^3)*b| + H/L^3) := by
  classical
  obtain ⟨r, hr, hcounts, hchange⟩ := exists_adjusted_counts (tileCount ℓ L) b H N hb hH hN
  have hs := sum_baseline_le hcounts hbound hbase
  have hm : 0 ≤ ℓ^3/L^3 := div_nonneg (pow_nonneg hℓ.le _) (pow_nonneg hL.le _)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (∑ i, if r i = b then 0 else 1 : ℕ) ≤
      (|(N : ℝ) - (tileCount ℓ L : ℝ)*b|+H)/(b : ℝ) :=
    (le_div_iff₀ hbR).2 hchange
  calc
    a L N ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i) := hbox r hr
    _ ≤ ℓ^3/L^3 * ((tileCount ℓ L : ℝ)*a ℓ b +
        2*M*((|(N : ℝ)-(tileCount ℓ L : ℝ)*b|+H)/(b : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hm
      exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*M by positivity)))
    _ = _ := by
      have heq : (N : ℝ)/L^3 - ((tileCount ℓ L : ℝ)/L^3)*b =
          ((N : ℝ)-(tileCount ℓ L : ℝ)*b)/L^3 := by ring
      rw [heq, abs_div, abs_of_pos (pow_pos hL 3)]
      ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem densityFilter_length (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => p.1) (densityFilter d) atTop := by
  have h : Tendsto (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3))
      (densityFilter d) (atTop ×ˢ 𝓝 d) := Filter.tendsto_comap
  simpa only [Function.comp_def] using
    (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 d) atTop).comp h

theorem densityFilter_density (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ)/p.1^3) (densityFilter d) (𝓝 d) :=
  tendsto_snd.comp (Filter.tendsto_comap : Tendsto _ (densityFilter d) _)

theorem tendsto_densityFilter_iff {α : Type u_1} {l : Filter α} {d : ℝ} {p : α → ℝ × ℕ} :
    Tendsto p l (densityFilter d) ↔
      Tendsto (fun x => (p x).1) l atTop ∧
      Tendsto (fun x => ((p x).2 : ℝ)/(p x).1^3) l (𝓝 d) := by
  rw [densityFilter, tendsto_comap_iff, tendsto_prod_iff']
  rfl

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d*L^3⌋₊)) atTop (densityFilter d) := by
  apply tendsto_densityFilter_iff.2
  exact ⟨tendsto_id, (tendsto_nat_floor_mul_div_atTop hd).comp
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0))⟩

instance densityFilter_neBot (d : ℝ) [Fact (0 ≤ d)] : (densityFilter d).NeBot :=
  (floor_density_tendsto (Fact.out : 0 ≤ d)).neBot

theorem tileCount_asymptotic {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Tendsto (fun L : ℝ => (tileCount ℓ L : ℝ)/L^3) atTop (𝓝 ((ℓ+2)⁻¹^3)) := by
  have hh : 0 ≤ (ℓ+2)⁻¹ := inv_nonneg.mpr (by linarith)
  have ht := (tendsto_nat_floor_mul_div_atTop hh).pow 3
  simpa only [tileCount, Nat.cast_pow, div_pow, div_eq_mul_inv, mul_comm,
    mul_pow, inv_pow] using ht

theorem length_inv_cube_tendsto (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.1^3)⁻¹) (densityFilter d) (𝓝 0) := by
  simpa only [Function.comp_def, ← inv_pow, zero_pow (by norm_num : 3 ≠ 0)] using
    (tendsto_inv_atTop_zero.pow 3).comp (densityFilter_length d)

theorem density_eventually_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ M : ℝ, ∀ᶠ p in densityFilter d, |a p.1 p.2| ≤ M := by
  obtain ⟨M, R, -, hR, hb⟩ := ha (d+1) (by linarith)
  refine ⟨M, ?_⟩
  filter_upwards [(densityFilter_length d).eventually (eventually_ge_atTop R),
    (densityFilter_density d).eventually (eventually_le_nhds (by linarith : d < d+1))] with p hp hpd
  exact hb p.1 hp p.2 ((div_le_iff₀ (pow_pos (hR.trans_le hp) 3)).1 hpd)

theorem densityFilter_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    (densityFilter d).IsBoundedUnder (· ≤ ·) (fun p => a p.1 p.2) ∧
    (densityFilter d).IsBoundedUnder (· ≥ ·) (fun p => a p.1 p.2) := by
  obtain ⟨M, hM⟩ := density_eventually_bounded ha hd
  exact ⟨⟨M, hM.mono (fun _ h => (abs_le.mp h).2)⟩,
    ⟨-M, hM.mono (fun _ h => (abs_le.mp h).1)⟩⟩

theorem limsup_box_comparison {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d ℓ M : ℝ} {b H : ℕ}
    (hd : 0 ≤ d) (hℓ : 0 < ℓ) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hcap : d < (ℓ+2)⁻¹^3 * H)
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
      (ℓ+2)⁻¹^3 * ℓ^3 * a ℓ b + (2*M*ℓ^3/(b : ℝ)) * |d-(ℓ+2)⁻¹^3*b| := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht := (tileCount_asymptotic hℓ.le).comp (densityFilter_length d)
  have hcap' := (densityFilter_density d).eventually_lt (ht.mul_const (H : ℝ)) hcap
  have hcomp : (fun p : ℝ × ℕ => a p.1 p.2) ≤ᶠ[densityFilter d]
      (fun p : ℝ × ℕ => ((tileCount ℓ p.1 : ℝ)/p.1^3)*ℓ^3*a ℓ b +
        (2*M*ℓ^3/(b : ℝ)) * (|(p.2 : ℝ)/p.1^3 - ((tileCount ℓ p.1 : ℝ)/p.1^3)*b| + H/p.1^3)) := by
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0), hcap'] with p hp hc
    have hnc : p.2 ≤ tileCount ℓ p.1 * H := by
      have hh : (p.2 : ℝ) < (tileCount ℓ p.1 : ℝ)*H := by
        apply (div_lt_div_iff_of_pos_right (pow_pos hp 3)).mp
        simpa only [div_mul_eq_mul_div, Function.comp_def] using hc
      exact_mod_cast hh.le
    exact adjusted_box_comparison a hℓ hp hM hb hH hnc
      (fun r hr => hr ▸ hbox ℓ p.1 hℓ hp r) hbound hbase
  have htail : Tendsto (fun p : ℝ × ℕ => (H : ℝ)/p.1^3) (densityFilter d) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (length_inv_cube_tendsto d).const_mul (H : ℝ)
  have hlim := ((ht.mul_const (ℓ^3)).mul_const (a ℓ b)).add
    ((((densityFilter_density d).sub (ht.mul_const (b : ℝ))).abs.add htail).const_mul (2*M*ℓ^3/(b : ℝ)))
  simp only [add_zero, Function.comp_def] at hlim
  have hle := limsup_le_limsup hcomp (densityFilter_bounded ha hd).2.isCobounded_le hlim.isBoundedUnder_le
  rwa [hlim.limsup_eq] at hle

 theorem dilution_tendsto_one :
    Tendsto (fun L : ℝ => (L+2)⁻¹^3*L^3) atTop (𝓝 1) := by
  have hh : Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 1) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 2))
        (by norm_num : (1 : ℝ)+2*0 ≠ 0))
    change Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 (1/(1+2*0))) at hh
    simpa only [mul_zero, add_zero, div_one] using hh
  have hpow : Tendsto (fun L : ℝ => (1/(1+2*L⁻¹))^3) atTop (𝓝 1) := by
    simpa only [one_pow] using hh.pow 3
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have h1 : 1+2*L⁻¹ ≠ 0 := by positivity
  have h2 : L+2 ≠ 0 := by linarith
  field_simp

theorem exists_density_limit {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) (𝓝 I) := by
  let : Fact (0 ≤ d) := ⟨hd.le⟩
  obtain ⟨hbup, hbdown⟩ := densityFilter_bounded ha hd.le
  obtain ⟨p, hpA, hp⟩ := exists_seq_tendsto_liminf hbup.isCobounded_ge hbdown
  obtain ⟨hpL, hpd⟩ := tendsto_densityFilter_iff.mp hp
  let D : ℝ := 4*d+4
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨M, R, hM, hR, hbound⟩ := ha D hD
  let H : ℕ → ℕ := fun j => ⌊D*(p j).1^3⌋₊
  have hα : Tendsto (fun j => ((p j).1+2)⁻¹^3*(p j).1^3) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using dilution_tendsto_one.comp hpL
  have hHratio : Tendsto (fun j => (H j : ℝ)/(p j).1^3) atTop (𝓝 D) := by
    exact (tendsto_nat_floor_mul_div_atTop hD.le).comp
      ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hpL)
  have hbd : Tendsto (fun j => ((p j).1+2)⁻¹^3*((p j).2 : ℝ)) atTop (𝓝 d) := by
    have hh : Tendsto (fun j => (((p j).1+2)⁻¹^3*(p j).1^3)*
        ((p j).2 : ℝ)/(p j).1^3) atTop (𝓝 d) := by
      simpa only [one_mul, mul_div_assoc] using hα.mul hpd
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hHd : Tendsto (fun j => ((p j).1+2)⁻¹^3*(H j : ℝ)) atTop (𝓝 D) := by
    have hh := hα.mul hHratio
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hcoef : Tendsto (fun j => 2*M*(p j).1^3/((p j).2 : ℝ)) atTop (𝓝 (2*M/d)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2*M) atTop (𝓝 (2*M))).div hpd hd.ne'
    change Tendsto (fun j => (2*M)/(((p j).2 : ℝ)/(p j).1^3)) atTop (𝓝 (2*M/d)) at hh
    simpa only [div_div_eq_mul_div] using hh
  have hfit : ∀ᶠ j in atTop, 2*(p j).2 ≤ H j := by
    have hh := (hpd.const_mul 2).eventually_lt hHratio (show 2*d < D by dsimp [D]; linarith)
    filter_upwards [hh, hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh' : (2 : ℝ)*(p j).2 < H j := by
      apply (div_lt_div_iff_of_pos_right (pow_pos hL 3)).mp
      simpa only [mul_div_assoc] using hj
    exact_mod_cast hh'.le
  have hpositive : ∀ᶠ j in atTop, 0 < (p j).2 := by
    filter_upwards [hpd.eventually (eventually_gt_nhds hd),
      hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh : (0 : ℝ) < (p j).2 := (div_pos_iff_of_pos_right (pow_pos hL 3)).1 hj
    exact_mod_cast hh
  have hcomp : ∀ᶠ j in atTop,
      limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
        ((p j).1+2)⁻¹^3 * (p j).1^3 * a (p j).1 (p j).2 +
        (2*M*(p j).1^3/((p j).2 : ℝ)) * |d-((p j).1+2)⁻¹^3*(p j).2| := by
    filter_upwards [hpL.eventually (eventually_ge_atTop R), hfit, hpositive,
      hHd.eventually (eventually_gt_nhds (show d < D by dsimp [D]; linarith))] with j hL hfit hb hcap
    have hLpos := hR.trans_le hL
    have hHle : (H j : ℝ) ≤ D*(p j).1^3 := Nat.floor_le (by positivity)
    apply limsup_box_comparison ha hbox hd.le hLpos hM.le hb hfit hcap
    · intro n hn
      exact (abs_le.mp (hbound (p j).1 hL n ((by exact_mod_cast hn : (n : ℝ) ≤ H j).trans hHle))).2
    · have hn : (p j).2 ≤ H j := by omega
      exact (abs_le.mp (hbound (p j).1 hL (p j).2
        ((by exact_mod_cast hn : ((p j).2 : ℝ) ≤ H j).trans hHle))).1
  have hlim := (hα.mul hpA).add (hcoef.mul (((tendsto_const_nhds (x := d)).sub hbd).abs))
  simp only [one_mul, sub_self, abs_zero, mul_zero, add_zero, Function.comp_def] at hlim
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hcomp
  exact ⟨liminf (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d),
    tendsto_of_le_liminf_of_limsup_le le_rfl hle hbup hbdown⟩

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_constant {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -Real.exp (β*B) ≤ finiteCanonical φ β L N := by
  have hc := (summable_grandPartition hφ hβ hL.le hstable 1 0).le_tsum N
    (fun n _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg φ β L n))
  have hc' : partition φ β L N ≤ grandPartition φ 1 β 0 L := by
    simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul, grandPartition] using hc
  have hZ := hc'.trans (grandPartition_le_exp hφ hβ hL.le hstable 1 0)
  simp only [mul_zero, zero_add] at hZ
  have hlog := Real.log_le_log (partition_pos hφ hβ hL hstable N) hZ
  rw [Real.log_exp] at hlog
  unfold finiteCanonical
  apply (le_div_iff₀ (pow_pos hL 3)).2
  nlinarith only [hlog]

theorem finiteCanonical_upper_trial {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹^3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    finiteCanonical φ β L N ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * (N : ℝ)/L^3 := by
  have hpos : 0 < trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q*N)) := by
    exact mul_pos (pow_pos (trialVolume_pos hq) N) (Real.exp_pos _)
  have hlow := partition_trial_lower hφ hq ht hβ hstable hcore hL hD hN
  have hlog := Real.log_le_log hpos hlow
  rw [Real.log_mul (pow_pos (trialVolume_pos hq) N).ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp] at hlog
  unfold finiteCanonical
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ L) 3)
  nlinarith only [hlog]

theorem finiteCanonical_densityBounded {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    DensityBounded (finiteCanonical φ β) := by
  intro D hD
  let q : ℝ := (2*(D+1))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hdmesh : D ≤ (2*q)⁻¹^3 := by
    have hh : (2*q)⁻¹ = D+1 := by dsimp [q]; field_simp
    rw [hh]
    nlinarith [sq_nonneg D]
  let C : ℝ := |β*trialEnergyConstant t q-Real.log (trialVolume q)|
  refine ⟨Real.exp (β*B)+C*D+1, 8*q, by dsimp [C]; positivity, by positivity, ?_⟩
  intro L hL N hN
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hlo := finiteCanonical_lower_constant hφ hβ hLpos hstable N
  have hup := finiteCanonical_upper_trial hφ hq ht hβ hstable hcore hL hdmesh hN
  have hup' : finiteCanonical φ β L N ≤ C*D := by
    calc
      _ ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * ((N : ℝ)/L^3) := by
        simpa only [mul_div_assoc] using hup
      _ ≤ C*((N : ℝ)/L^3) := mul_le_mul_of_nonneg_right (le_abs_self _)
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hLpos.le 3))
      _ ≤ C*D := mul_le_mul_of_nonneg_left ((div_le_iff₀ (pow_pos hLpos 3)).2 hN) (abs_nonneg _)
  apply abs_le.mpr
  have hCD : 0 ≤ C*D := mul_nonneg (abs_nonneg _) hD.le
  have he := (Real.exp_pos (β*B)).le
  constructor <;> linarith

theorem finiteCanonical_hasBoxInequality {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0) : HasBoxInequality (finiteCanonical φ β) := by
  intro ℓ L hℓ hL r
  classical
  let e : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) ≃ Fin (tileCount ℓ L) :=
    Fintype.equivFinOfCardEq (by simp [tileCount])
  have htile := partition_tiling_lower hφ hβ hℓ.le hL.le hstable hsign (fun i => r (e i))
  rw [e.sum_comp] at htile
  have hprod := e.prod_comp (fun i => partition φ β ℓ (r i))
  rw [hprod] at htile
  have hlog := Real.log_le_log (Finset.prod_pos (fun i _ => partition_pos hφ hβ hℓ hstable (r i))) htile
  rw [Real.log_prod (fun i _ => (partition_pos hφ hβ hℓ hstable (r i)).ne')] at hlog
  unfold finiteCanonical
  calc
    -Real.log (partition φ β L (∑ i, r i))/L^3 ≤ -(∑ i, Real.log (partition φ β ℓ (r i)))/L^3 :=
      div_le_div_of_nonneg_right (neg_le_neg hlog) (pow_nonneg hL.le 3)
    _ = ℓ^3/L^3 * ∑ i, -Real.log (partition φ β ℓ (r i))/ℓ^3 := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
      field_simp

theorem exists_canonical_density_limit {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter d) (𝓝 I) := by
  apply exists_density_limit (finiteCanonical_densityBounded hφ ht hβ hstable hcore)
    (finiteCanonical_hasBoxInequality hφ hβ hstable _) hd
  intro r hr
  exact (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)

theorem finiteCanonical_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -β * B * ((N : ℝ) / L ^ 3) + ((N : ℝ) / L ^ 3) * Real.log ((N : ℝ) / L ^ 3)
      - (N : ℝ) / L ^ 3 ≤ finiteCanonical φ β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hh := neg_log_partition_lower hφ hβ hL hstable hN
    (fun x _ => hstable N x)
  have hh' := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  calc
    _ = (β * (-B * (N : ℝ)) + N * Real.log ((N : ℝ) / L ^ 3) - N) / L ^ 3 := by ring
    _ ≤ _ := hh'

theorem finiteCanonical_tendsto_zero_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter 0) (𝓝 0) := by
  have hden := densityFilter_density 0
  have hlo : Tendsto (fun p : ℝ × ℕ =>
      -β * B * ((p.2 : ℝ) / p.1 ^ 3) + ((p.2 : ℝ) / p.1 ^ 3) *
        Real.log ((p.2 : ℝ) / p.1 ^ 3) - (p.2 : ℝ) / p.1 ^ 3)
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero, Real.log_zero, add_zero, sub_zero, Function.comp_def] using
      ((hden.const_mul (-β * B)).add (Real.continuous_mul_log.tendsto 0 |>.comp hden)).sub hden
  let C := β * trialEnergyConstant t (1/2) - Real.log (trialVolume (1/2))
  have hup : Tendsto (fun p : ℝ × ℕ => C * ((p.2 : ℝ) / p.1 ^ 3))
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero] using hden.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [(densityFilter_length 0).eventually (eventually_gt_atTop 0)] with p hp
    exact finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  · filter_upwards [(densityFilter_length 0).eventually (eventually_ge_atTop 4),
      hden.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with p hp hpd
    have hL : 0 < p.1 := by linarith
    have hh := finiteCanonical_upper_trial hφ (by norm_num : (0 : ℝ) < 1 / 2)
      ht hβ hstable hcore (by linarith : 8*(1/2 : ℝ) ≤ p.1)
      (by norm_num : (1 : ℝ) ≤ (2*(1/2))⁻¹^3)
      ((div_le_iff₀ (pow_pos hL 3)).1 hpd)
    simpa only [C, mul_div_assoc] using hh

theorem finiteCanonical_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2)
      (densityFilter d) (𝓝 (canonicalDensity φ β d)) := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  obtain hzero | hpos := hd.eq_or_lt
  · subst d
    have hz := finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore
    simpa only [canonicalDensity, hz.liminf_eq] using hz
  · obtain ⟨I, hI⟩ := exists_canonical_density_limit hφ ht hβ hstable hcore hpos
    simpa only [canonicalDensity, hI.liminf_eq] using hI

@[simp] theorem canonicalDensity_zero {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) : canonicalDensity φ β 0 = 0 := by
  let : Fact (0 ≤ (0 : ℝ)) := ⟨le_rfl⟩
  exact (finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore).liminf_eq

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set

namespace ContinuumTemperature

theorem tsum_le_low_sector_add_tail {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) {M : ℕ} {A : ℝ}
    (hlow : ∀ n, n < M → w n ≤ A) (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    ∑' n, w n ≤ (M : ℝ)*A + ∑' n, b n := by
  have hst : Summable (fun n : ℕ => w (n+M)) :=
    hw.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbt : Summable (fun n : ℕ => b (n+M)) :=
    hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have ht : (∑' n : ℕ, w (n+M)) ≤ ∑' n : ℕ, b (n+M) :=
    hst.tsum_le_tsum (fun n => hhigh _ (Nat.le_add_left M n)) hbt
  have htail : (∑' n : ℕ, b (n+M)) ≤ ∑' n, b n := by
    rw [← hb.sum_add_tsum_nat_add M]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => hb0 n))
  have hsum : (∑ n ∈ Finset.range M, w n) ≤ (M : ℝ)*A := by
    calc
      (∑ n ∈ Finset.range M, w n) ≤ ∑ n ∈ Finset.range M, A :=
        Finset.sum_le_sum (fun n hn => hlow n (Finset.mem_range.mp hn))
      _ = _ := by simp
  rw [← hw.sum_add_tsum_nat_add M]
  exact add_le_add hsum (ht.trans htail)

theorem log_affine_cube_div_tendsto_zero {D C : ℝ} (hD : 0 < D) :
    Tendsto (fun L : ℝ => Real.log (D*L^3+C)/L^3) atTop (𝓝 0) := by
  have hv : Tendsto (fun L : ℝ => L^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun L : ℝ => D*L^3+C) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop C (hv.const_mul_atTop hD)
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hz
  have hi : Tendsto (fun L : ℝ => (L^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hv
  have hr : Tendsto (fun L : ℝ => D+C*(L^3)⁻¹) atTop (𝓝 D) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hi.const_mul C)
  have hh := hlog.mul hr
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [hv.eventually (eventually_gt_atTop 0), hz.eventually (eventually_gt_atTop 0)] with L hL hzL
  change Real.log (D*L^3+C)/(D*L^3+C)*(D+C*(L^3)⁻¹) = _
  have hn : L ≠ 0 := by rintro rfl; simp at hL
  field_simp [hn, ne_of_gt hzL]

theorem log_tsum_div_le {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) (hpos : 0 < ∑' n, w n) {M : ℕ} (hM : 0 < M)
    {V c : ℝ} (hV : 0 < V) (hc : 0 ≤ c)
    (hlow : ∀ n, n < M → w n ≤ Real.exp (V*c))
    (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    Real.log (∑' n, w n)/V ≤ c + Real.log ((M : ℝ)+∑' n, b n)/V := by
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have he : 1 ≤ Real.exp (V*c) := Real.one_le_exp (mul_nonneg hV.le hc)
  have hbound := tsum_le_low_sector_add_tail hw hb hb0 hlow hhigh
  have hbound' : ∑' n, w n ≤ ((M : ℝ)+∑' n, b n)*Real.exp (V*c) := by
    have hh := mul_le_mul_of_nonneg_left he hbS
    nlinarith only [hbound, hh]
  have hp : 0 < (M : ℝ)+∑' n, b n := by positivity
  have hlog := Real.log_le_log hpos hbound'
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  calc
    Real.log (∑' n, w n)/V ≤ (Real.log ((M : ℝ)+∑' n, b n)+V*c)/V :=
      div_le_div_of_nonneg_right hlog hV.le
    _ = _ := by field_simp; ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplacePrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem density_compact_eventually {K : Set ℝ} (hK : IsCompact K)
    {P : ℝ × ℕ → Prop} (hP : ∀ d ∈ K, ∀ᶠ p in densityFilter d, P p) :
    ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ K → P (L,n) := by
  have hp : ∀ᶠ p in Filter.comap
      (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝ˢ K), P p := by
    rw [hK.prod_nhdsSet_eq_biSup, comap_iSup]
    simp only [comap_iSup, eventually_iSup]
    exact hP
  obtain ⟨S, hS, hsub⟩ := Filter.mem_comap.mp hp
  obtain ⟨T, hT, U, hU, hTU⟩ := Filter.mem_prod_iff.mp hS
  filter_upwards [hT] with L hL
  intro n hn
  exact hsub (hTU ⟨hL, (subset_of_mem_nhdsSet hU) hn⟩)

theorem canonicalDensity_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    d*Real.log d-(β*B+1)*d ≤ canonicalDensity φ β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have hlim := finiteCanonical_tendsto hφ ht hβ hstable hcore hd
  have he := ((Real.continuous_mul_log.continuousAt.tendsto).comp
    (densityFilter_density d)).sub ((densityFilter_density d).const_mul (β*B+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  have hh := finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  dsimp only [Function.comp_def] at *
  nlinarith only [hh]

theorem entropy_dual_bound (c : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (c+1)*d-d*Real.log d ≤ Real.exp c := by
  obtain rfl | hd := hd.eq_or_lt
  · simp only [mul_zero, zero_mul, sub_self]
    exact (Real.exp_pos c).le
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c-Real.log d)) hd.le
  rw [Real.exp_sub, Real.exp_log hd, div_mul_cancel₀ _ hd.ne'] at hh
  nlinarith only [hh]

theorem canonicalPressure_bddAbove {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    BddAbove ((fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*B), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem laplace_low_sector {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {D S ε : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hD : 0 < D) (hε : 0 < ε)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d))) :
    ∀ᶠ L in atTop, ∀ n : ℕ, n < ⌊D*L^3⌋₊+1 →
      w L n ≤ Real.exp (L^3*(S+ε)) := by
  have he : ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ Icc 0 D →
      Real.log (w L n)/L^3 < S+ε := by
    apply density_compact_eventually (K := Icc 0 D)
      (P := fun p => Real.log (w p.1 p.2)/p.1^3 < S+ε) isCompact_Icc
    intro d hd
    apply (hlim d hd.1).eventually_lt_const
    linarith [hF d hd.1]
  filter_upwards [he, eventually_gt_atTop 0] with L hL hp
  intro n hn
  have hn' : (n : ℝ) ≤ D*L^3 :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn)).trans (Nat.floor_le (by positivity))
  have hr : (n : ℝ)/L^3 ∈ Icc 0 D :=
    ⟨div_nonneg (Nat.cast_nonneg n) (pow_pos hp 3).le, (div_le_iff₀ (pow_pos hp 3)).2 hn'⟩
  apply (Real.log_le_iff_le_exp (hw L hp n)).1
  have hh := (div_lt_iff₀ (pow_pos hp 3)).1 (hL n hr)
  nlinarith only [hh]

theorem laplace_upper_eventually {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ}
    {D S : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hS : 0 ≤ S)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    ∀ q > S, ∀ᶠ L in atTop, Real.log (∑' n, w L n)/L^3 < q := by
  intro q hq
  let ε := (q-S)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := log_affine_cube_div_tendsto_zero (C := 1+∑' n, b n) hD
  have he := hlog.eventually_lt_const hε
  filter_upwards [laplace_low_sector hw hD hε hF hlim, htail, he,
    eventually_gt_atTop 0] with L hlow hhigh hsmall hL
  let M : ℕ := ⌊D*L^3⌋₊+1
  have hV : 0 < L^3 := pow_pos hL 3
  have hpos : 0 < ∑' n, w L n :=
    (hw L hL 0).trans_le ((hsum L hL).le_tsum 0 (fun n _ => (hw L hL n).le))
  have hh := log_tsum_div_le (hsum L hL) hb hb0 hpos (Nat.succ_pos _ : 0 < M)
    hV (show 0 ≤ S+ε by linarith) hlow (fun n hn => hhigh n (by
      apply (le_div_iff₀ hV).2
      have hm : D*L^3 < (M : ℝ) := by simpa [M] using Nat.lt_floor_add_one (D*L^3)
      exact hm.le.trans (Nat.cast_le.mpr hn)))
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have hM : (M : ℝ)+∑' n, b n ≤ D*L^3+(1+∑' n, b n) := by
    have hf := Nat.floor_le (mul_nonneg hD.le hV.le)
    dsimp [M]
    push_cast
    linarith
  have hMpos : 0 < (M : ℝ)+∑' n, b n := by
    have hp : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    linarith
  have hl := div_le_div_of_nonneg_right (Real.log_le_log hMpos hM) hV.le
  dsimp [ε] at *
  linarith only [hh, hl, hsmall]

theorem laplace_principle {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  have hnon : (F '' Ici 0).Nonempty := ⟨F 0, ⟨0, by simp, rfl⟩⟩
  have hF : ∀ d, 0 ≤ d → F d ≤ sSup (F '' Ici 0) :=
    fun d hd => le_csSup hbdd ⟨d, hd, rfl⟩
  have hS : 0 ≤ sSup (F '' Ici 0) := by simpa [hF0] using hF 0 le_rfl
  apply tendsto_order.2
  constructor
  · intro q hq
    obtain ⟨_, ⟨d, hd, rfl⟩, hqd⟩ := exists_lt_of_lt_csSup hnon hq
    have hdlim := (hlim d hd).comp (floor_density_tendsto hd)
    filter_upwards [hdlim.eventually_const_lt hqd, eventually_gt_atTop 0] with L hL hp
    have hh := (hsum L hp).le_tsum ⌊d*L^3⌋₊ (fun n _ => (hw L hp n).le)
    exact hL.trans_le (div_le_div_of_nonneg_right (Real.log_le_log (hw L hp _) hh)
      (pow_pos hp 3).le)
  · exact laplace_upper_eventually hw hsum hb hb0 hD hS hF hlim htail

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_grand_weight_div {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L μ : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    Real.log (Real.exp (μ*N)*partition φ β L N)/L^3 =
      μ*((N : ℝ)/L^3)-finiteCanonical φ β L N := by
  rw [Real.log_mul (Real.exp_pos _).ne' (partition_pos hφ hβ hL hstable N).ne',
    Real.log_exp]
  unfold finiteCanonical
  ring

theorem grand_weight_high_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L μ : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ}
    (hN : Real.exp (μ+β*B+2) ≤ (N : ℝ)/L^3) :
    Real.exp (μ*N)*partition φ β L N ≤ (Real.exp (-1))^N := by
  have hden : 0 ≤ (N : ℝ)/L^3 := div_nonneg (Nat.cast_nonneg _) (pow_pos hL 3).le
  have hlog := Real.log_le_log (Real.exp_pos (μ+β*B+2)) hN
  rw [Real.log_exp] at hlog
  have he := finiteCanonical_lower_entropy hφ hβ hL hstable N
  have hm := mul_le_mul_of_nonneg_right hlog hden
  have hbound : μ*((N : ℝ)/L^3)-finiteCanonical φ β L N ≤ -((N : ℝ)/L^3) := by
    nlinarith only [he, hm]
  rw [← log_grand_weight_div hφ hβ hL hstable N, ← neg_div] at hbound
  have hh := (div_le_div_iff_of_pos_right (pow_pos hL 3)).1 hbound
  have hw : 0 < Real.exp (μ*N)*partition φ β L N :=
    mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hstable N)
  rw [← Real.exp_nat_mul]
  apply (Real.log_le_iff_le_exp hw).1
  simpa using hh

theorem grandPartition_pressure_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun L => Real.log (grandPartition φ 1 β μ L)/L^3) atTop
      (𝓝 (canonicalPressure φ β μ)) := by
  have hw : ∀ L > 0, ∀ N : ℕ, 0 < Real.exp (μ*N)*partition φ β L N :=
    fun L hL N => mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hstable N)
  have hs : ∀ L > 0, Summable (fun N : ℕ => Real.exp (μ*N)*partition φ β L N) := by
    intro L hL
    simpa only [one_mul] using summable_grandPartition hφ hβ hL.le hstable 1 μ
  have hb : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  have hz : μ*0-canonicalDensity φ β 0 = 0 := by
    rw [canonicalDensity_zero hφ ht hβ hstable hcore]; ring
  have hlim : ∀ d, 0 ≤ d →
      Tendsto (fun p : ℝ × ℕ => Real.log (Real.exp (μ*p.2)*partition φ β p.1 p.2)/p.1^3)
        (densityFilter d) (𝓝 (μ*d-canonicalDensity φ β d)) := by
    intro d hd
    have hh := ((densityFilter_density d).const_mul μ).sub
      (finiteCanonical_tendsto hφ ht hβ hstable hcore hd)
    apply hh.congr'
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
    exact (log_grand_weight_div hφ hβ hp hstable p.2).symm
  have ht' : ∀ᶠ L in atTop, ∀ N : ℕ, Real.exp (μ+β*B+2) ≤ (N : ℝ)/L^3 →
      Real.exp (μ*N)*partition φ β L N ≤ (Real.exp (-1))^N := by
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact fun _ hN => grand_weight_high_density hφ hβ hL hstable hN
  have hh := laplace_principle hw hs hb (fun n => (pow_pos (Real.exp_pos _) n).le)
    (Real.exp_pos (μ+β*B+2)) hz (canonicalPressure_bddAbove hφ ht hβ hstable hcore) hlim ht'
  simpa only [grandPartition, one_mul, canonicalPressure] using hh

theorem physicalPressure_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B h : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun L => Real.log (grandPartition φ t β h L)/(t*L^3)) atTop
      (𝓝 (physicalPressure φ t (β,h))) := by
  change Tendsto _ atTop (𝓝 (canonicalPressure φ β (t*h)/t))
  have hh := (grandPartition_pressure_tendsto hφ ht hβ hstable hcore (μ := t*h)).div_const t
  convert hh using 1
  ext L
  simp only [grandPartition, one_mul]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem CellLowerBound.mono {t : ℝ} {σ R : ℕ → ℝ} {U V : Space → Space → ℝ}
    (hU : CellLowerBound t σ R U) (hUV : ∀ x y, U x y ≤ V x y) : CellLowerBound t σ R V :=
  fun x y => (hU x y).trans (hUV x y)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem physicalProfile_le_core {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    physicalProfile t σ R r ≤ coreProfile t r :=
  sub_le_self _ (attraction_nonneg ht hσ hR r)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CoerciveCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_coercive {t β L : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (N : ℕ) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3)*((N : ℝ)/L^3)^2 +
      ((N : ℝ)/L^3)*Real.log ((N : ℝ)/L^3)-(β*t^2/2+1)*((N : ℝ)/L^3) ≤
      finiteCanonical (physicalProfile t σ R) β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  have hh := neg_log_partition_lower hφ hβ hL hst hN
    (physicalProfile_energy_coercive ht hL.le hσ hR hs hsmall N)
  have hd := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  convert hd using 1; try rfl
  field_simp
  ring

theorem canonicalDensity_lower_coercive {t β d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (hd : 0 ≤ d) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)*d^2 +
      d*Real.log d-(β*t^2/2+1)*d ≤ canonicalDensity (physicalProfile t σ R) β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0 hσ hR hs hsmall
  have hcore (r : ℝ) (_ : 0 < r) := physicalProfile_le_core ht0 hσ hR r
  have hlim := finiteCanonical_tendsto hφ ht hβ hst hcore hd
  have hi := tendsto_inv_atTop_zero.comp (densityFilter_length d)
  have hc : Tendsto (fun p : ℝ × ℕ =>
      (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/p.1)^3)
      (densityFilter d) (𝓝 ((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)) := by
    have hh := (tendsto_const_nhds (x := t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)).div
      ((tendsto_const_nhds.add (hi.const_mul 2)).pow 3)
      (by norm_num : (4+2*(0 : ℝ))^3 ≠ 0)
    change Tendsto (fun p : ℝ × ℕ =>
      (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2*(p.1)⁻¹)^3)
      (densityFilter d) (𝓝 ((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/((4+2*(0 : ℝ))^3))) at hh
    simpa only [mul_zero, add_zero, div_eq_mul_inv, Function.comp_def, Pi.mul_apply, Pi.inv_apply,
      show (4 : ℝ)^3 = 64 by norm_num] using hh
  have he := (((hc.const_mul β).mul ((densityFilter_density d).pow 2)).add
    (Real.continuous_mul_log.continuousAt.tendsto.comp (densityFilter_density d))).sub
    ((densityFilter_density d).const_mul (β*t^2/2+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  exact finiteCanonical_lower_coercive ht0 hβ hp hσ hR hs hsmall p.2

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem quadraticPressure_bddAbove {t β μ a : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)) :
    BddAbove ((fun d : ℝ => μ*d+a*d^2-canonicalDensity (physicalProfile t σ R) β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*t^2/2), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_coercive ht hβ hσ hR hs hsmall hd
  have he := entropy_dual_bound (μ+β*t^2/2) hd
  have hq := mul_le_mul_of_nonneg_right ha (sq_nonneg d)
  linarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ThermodynamicExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

theorem sum_twoBoxCounts {M : Type u_1} [AddCommMonoid M] (f : ℕ → M)
    {K k : ℕ} (hk : k ≤ K) (n₁ n₂ : ℕ) :
    ∑ i, f (twoBoxCounts K k n₁ n₂ i) = k • f n₁ + (K-k) • f n₂ := by
  induction K generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    simp [hk0]
  | succ K ih =>
    cases k with
    | zero => simp [twoBoxCounts]
    | succ k =>
      have hkle : k ≤ K := by omega
      simp only [twoBoxCounts, Fin.sum_univ_succ, Fin.val_zero, Nat.zero_lt_succ,
        ite_true, Fin.val_succ, Nat.succ_lt_succ_iff]
      rw [show (∑ i : Fin K, f (if (i : ℕ) < k then n₁ else n₂)) =
          k • f n₁ + (K-k) • f n₂ from ih hkle]
      simp only [Nat.succ_sub_succ_eq_sub, succ_nsmul]
      abel

theorem tileCount_exact {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : ℕ) :
    tileCount ℓ ((k : ℝ) * (ℓ+2)) = k^3 := by
  have hh : ℓ+2 ≠ 0 := by linarith
  simp [tileCount, mul_div_cancel_right₀ _ hh]

theorem mixCount_le {θ : ℝ} (hθ1 : θ ≤ 1) (n : ℕ) : mixCount θ n ≤ n^3 := by
  have hx : θ*(n : ℝ)^3 ≤ (n : ℝ)^3 :=
    mul_le_of_le_one_left (pow_nonneg (Nat.cast_nonneg n) 3) hθ1
  simpa only [mixCount, ← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_mono hx

theorem tendsto_mixCount {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun n : ℕ => (mixCount θ n : ℝ)/(n : ℝ)^3) atTop (𝓝 θ) :=
  (tendsto_nat_floor_mul_div_atTop hθ).comp
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop)

theorem tendsto_mixSide : Tendsto mixSide atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [] with n
  dsimp [mixSide]
  nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

theorem mixTotal_ratio {θ d₁ d₂ : ℝ} (hθ1 : θ ≤ 1) {n : ℕ} (hn : 0 < n) :
    (mixTotal θ d₁ d₂ n : ℝ)/(mixSide n)^3 =
      ((n : ℝ)+2)⁻¹^3*(n : ℝ)^3 *
        (((mixCount θ n : ℝ)/(n : ℝ)^3)*((mixCount d₁ n : ℝ)/(n : ℝ)^3) +
        (1-(mixCount θ n : ℝ)/(n : ℝ)^3)*((mixCount d₂ n : ℝ)/(n : ℝ)^3)) := by
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  unfold mixTotal mixSide
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (mixCount_le hθ1 n), Nat.cast_pow]
  field_simp

theorem tendsto_mixTotal {θ d₁ d₂ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    Tendsto (fun n : ℕ => (mixTotal θ d₁ d₂ n : ℝ)/(mixSide n)^3)
      atTop (𝓝 (θ*d₁+(1-θ)*d₂)) := by
  have hdil := dilution_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hdil.mul (((tendsto_mixCount hθ).mul (tendsto_mixCount hd₁)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mixCount hθ)).mul (tendsto_mixCount hd₂)))
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (mixTotal_ratio hθ1 hn).symm

theorem mixBox_inequality {a : ℝ → ℕ → ℝ} (hbox : HasBoxInequality a)
    {θ d₁ d₂ : ℝ} (hθ1 : θ ≤ 1) {n : ℕ} (hnpos : 0 < n) :
    a (mixSide n) (mixTotal θ d₁ d₂ n) ≤
      ((n : ℝ)+2)⁻¹^3*(n : ℝ)^3 *
        (((mixCount θ n : ℝ)/(n : ℝ)^3)*a (n : ℝ) (mixCount d₁ n) +
        (1-(mixCount θ n : ℝ)/(n : ℝ)^3)*a (n : ℝ) (mixCount d₂ n)) := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hcount : tileCount (n : ℝ) (mixSide n) = n^3 := tileCount_exact hnp.le n
  have hk : mixCount θ n ≤ n^3 := mixCount_le hθ1 n
  have hk' : mixCount θ n ≤ tileCount (n : ℝ) (mixSide n) := hcount.symm ▸ hk
  have hx := hbox (n : ℝ) (mixSide n) hnp (by dsimp [mixSide]; positivity)
    (twoBoxCounts (tileCount (n : ℝ) (mixSide n)) (mixCount θ n)
      (mixCount d₁ n) (mixCount d₂ n))
  rw [sum_twoBoxCounts (fun m : ℕ => m) hk', sum_twoBoxCounts (a (n : ℝ)) hk'] at hx
  simp only [nsmul_eq_mul, hcount] at hx
  change a (mixSide n) (mixTotal θ d₁ d₂ n) ≤ _ at hx
  refine hx.trans_eq ?_
  unfold mixSide
  rw [Nat.cast_sub hk, Nat.cast_pow]
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem convexOn_of_box_limits {a : ℝ → ℕ → ℝ} {F : ℝ → ℝ}
    (hbox : HasBoxInequality a)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => a p.1 p.2)
      (densityFilter d) (𝓝 (F d))) : ConvexOn ℝ (Ici 0) F := by
  refine ⟨convex_Ici _, ?_⟩
  intro d₁ hd₁ d₂ hd₂ θ η hθ hη hsum
  simp only [smul_eq_mul]
  have hθ1 : θ ≤ 1 := by linarith
  have hηeq : η = 1-θ := by linarith
  subst η
  have hd : 0 ≤ θ*d₁+(1-θ)*d₂ := add_nonneg (mul_nonneg hθ hd₁) (mul_nonneg hη hd₂)
  have hdil := dilution_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hseq : Tendsto (fun n : ℕ => (mixSide n, mixTotal θ d₁ d₂ n))
      atTop (densityFilter (θ*d₁+(1-θ)*d₂)) :=
    tendsto_densityFilter_iff.mpr ⟨tendsto_mixSide, tendsto_mixTotal hθ hθ1 hd₁ hd₂⟩
  have hvN : Tendsto (fun n => a (mixSide n) (mixTotal θ d₁ d₂ n))
      atTop (𝓝 (F (θ*d₁+(1-θ)*d₂))) := (hlim _ hd).comp hseq
  have hva₁ : Tendsto (fun n : ℕ => a (n : ℝ) (mixCount d₁ n)) atTop (𝓝 (F d₁)) :=
    (hlim _ hd₁).comp ((floor_density_tendsto hd₁).comp tendsto_natCast_atTop_atTop)
  have hva₂ : Tendsto (fun n : ℕ => a (n : ℝ) (mixCount d₂ n)) atTop (𝓝 (F d₂)) :=
    (hlim _ hd₂).comp ((floor_density_tendsto hd₂).comp tendsto_natCast_atTop_atTop)
  have hR := hdil.mul (((tendsto_mixCount hθ).mul hva₁).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mixCount hθ)).mul hva₂))
  simp only [one_mul] at hR
  apply le_of_tendsto_of_tendsto hvN hR
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
  exact mixBox_inequality hbox hθ1 hnpos

theorem convexOn_canonicalDensity {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ (Ici 0) (canonicalDensity φ β) := by
  apply convexOn_of_box_limits
    (finiteCanonical_hasBoxInequality hφ hβ hstable (fun r hr =>
      (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)))
  exact fun d hd => finiteCanonical_tendsto hφ ht hβ hstable hcore hd

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convex_rightDeriv_support {f : ℝ → ℝ} {S : Set ℝ} (hf : ConvexOn ℝ S f)
    {x : ℝ} (hx : x ∈ interior S) :
    ∀ y ∈ S, f x + derivWithin f (Ioi x) x * (y-x) ≤ f y := by
  intro y hy
  obtain hxy | rfl | hyx := lt_trichotomy x y
  · have hh := hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hxy)).1 hh
    linarith
  · simp
  · have hh := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hyx)).1 hh
    nlinarith only [hh']

theorem canonicalPressure_nonneg {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    0 ≤ canonicalPressure φ β μ := by
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
    (mem_image_of_mem (fun d : ℝ => μ*d-canonicalDensity φ β d) (show 0 ∈ Ici (0 : ℝ) by simp))
  simpa only [canonicalDensity_zero hφ ht hβ hstable hcore, mul_zero, sub_zero,
    canonicalPressure] using hh

theorem canonicalPressure_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    canonicalPressure φ β μ ≤ Real.exp (μ+β*B) := by
  unfold canonicalPressure
  apply csSup_le (s := (fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)
      ⟨μ*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem canonical_fenchel_inequality {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    μ*d-canonicalPressure φ β μ ≤ canonicalDensity φ β d := by
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
    (mem_image_of_mem (fun d : ℝ => μ*d-canonicalDensity φ β d) hd)
  change μ*d-canonicalDensity φ β d ≤ canonicalPressure φ β μ at hh
  linarith

theorem canonical_fenchel_attained {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 < d) :
    ∃ μ, canonicalPressure φ β μ = μ*d-canonicalDensity φ β d := by
  let μ := derivWithin (canonicalDensity φ β) (Ioi d) d
  have hs := convex_rightDeriv_support (convexOn_canonicalDensity hφ ht hβ hstable hcore)
    (show d ∈ interior (Ici (0 : ℝ)) by simpa using hd)
  refine ⟨μ, le_antisymm ?_ ?_⟩
  · unfold canonicalPressure
    apply csSup_le (s := (fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)
      ⟨μ*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
    rintro _ ⟨c, hc, rfl⟩
    have hh := hs c hc
    dsimp [μ]
    nlinarith only [hh]
  · exact le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
      ⟨d, hd.le, rfl⟩

theorem canonical_partialConjugate {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsPartialConjugate (fun x => canonicalPressure φ x.1 x.2) (canonicalDensity φ) := by
  intro β d hβ hd
  constructor
  · rintro _ ⟨μ, rfl⟩
    exact canonical_fenchel_inequality hφ ht hβ.le hstable hcore hd
  · intro z hz
    obtain rfl | hd := hd.eq_or_lt
    · rw [canonicalDensity_zero hφ ht hβ.le hstable hcore]
      by_contra hneg
      have hzneg : z < 0 := lt_of_not_ge hneg
      let μ := Real.log (-z/2)-β*B
      have hQ := canonicalPressure_le_exp hφ ht hβ.le hstable hcore (μ := μ)
      have he : Real.exp (μ+β*B) = -z/2 := by
        dsimp [μ]
        rw [sub_add_cancel, Real.exp_log (by linarith)]
      rw [he] at hQ
      have hbound := hz (mem_range_self μ)
      dsimp at hbound
      linarith
    · obtain ⟨μ, hμ⟩ := canonical_fenchel_attained hφ ht hβ.le hstable hcore hd
      have hh := hz (mem_range_self μ)
      dsimp at hh
      rw [hμ] at hh
      linarith

theorem physical_partialConjugate {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsPartialConjugate (physicalPressure φ t) (physicalCanonical φ t) := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  intro β d hβ hd
  have hh := canonical_partialConjugate hφ ht hstable hcore β d hβ hd
  constructor
  · rintro _ ⟨h, rfl⟩
    have hz := hh.1 (mem_range_self (t*h))
    dsimp [physicalPressure, physicalCanonical]
    apply (le_div_iff₀ ht0).2
    have hne : t ≠ 0 := ht0.ne'
    field_simp [hne]
    dsimp only at hz
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hz
  · intro z hz
    apply (div_le_iff₀ ht0).2
    apply hh.2
    rintro _ ⟨μ, rfl⟩
    have hm := hz (mem_range_self (μ/t))
    dsimp [physicalPressure] at hm
    rw [mul_div_cancel₀ _ ht0.ne'] at hm
    have hm' := mul_le_mul_of_nonneg_right hm ht0.le
    dsimp [physicalCanonical]
    field_simp [ht0.ne'] at hm'
    nlinarith only [hm']

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convexOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ pressureDomain (physicalPressure φ t) := by
  have hcD : Convex ℝ pressureDomain :=
    (convexOn_log_grandPartition hφ (by norm_num : (0 : ℝ) < 1) hstable t).1
  refine ⟨hcD, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hcD hx hy ha hb hab
  have hl := physicalPressure_tendsto hφ ht (le_of_lt hz) hstable hcore (h := (a • x+b • y).2)
  have hr := ((physicalPressure_tendsto hφ ht (le_of_lt hx) hstable hcore (h := x.2)).const_mul a).add
    ((physicalPressure_tendsto hφ ht (le_of_lt hy) hstable hcore (h := y.2)).const_mul b)
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hh := (convexOn_log_grandPartition hφ hL hstable t).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh
  have hV : 0 ≤ t*L^3 := mul_nonneg (by linarith) (pow_pos hL 3).le
  have hbound := div_le_div_of_nonneg_right hh hV
  simpa only [add_div, mul_div_assoc] using hbound

theorem isOpen_pressureDomain : IsOpen pressureDomain :=
  isOpen_lt continuous_const continuous_fst

theorem continuousOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ContinuousOn (physicalPressure φ t) pressureDomain :=
  (convexOn_physicalPressure hφ ht hstable hcore).continuousOn isOpen_pressureDomain

theorem monotone_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B β : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Monotone (fun h => physicalPressure φ t (β,h)) := by
  intro h k hhk
  have ht0 : 0 < t := by linarith
  apply div_le_div_of_nonneg_right _ ht0.le
  unfold canonicalPressure
  apply csSup_le (s := (fun d : ℝ => t*h*d-canonicalDensity φ β d) '' Ici 0)
    ⟨t*h*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := t*k))
    (mem_image_of_mem (fun d : ℝ => t*k*d-canonicalDensity φ β d) hd)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhk ht0.le) hd
  exact (sub_le_sub_right hmul _).trans hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma convolution_isLUB {Q H : ℝ → ℝ} {P β h a : ℝ} (hba : 0 ≤ β*a)
    (hQ : ∀ k, IsLUB ((fun d => k*d-H d) '' Ici 0) (Q k))
    (hP : IsLUB ((fun d => h*d+β*a*d^2/2-H d) '' Ici 0) P) :
    IsLUB (range (fun d => Q (h+β*a*d)-β*a*d^2/2)) P := by
  constructor
  · rintro _ ⟨d,rfl⟩
    have hu : Q (h+β*a*d) ≤ P+β*a*d^2/2 := by
      apply (hQ _).2
      rintro _ ⟨r,hr,rfl⟩
      have hh := hP.1 (mem_image_of_mem (fun r => h*r+β*a*r^2/2-H r) hr)
      have hs := mul_nonneg hba (sq_nonneg (r-d))
      nlinarith
    linarith
  · intro z hz
    apply hP.2
    rintro _ ⟨d,hd,rfl⟩
    have hh := (hQ (h+β*a*d)).1 (mem_image_of_mem (fun r => (h+β*a*d)*r-H r) hd)
    have hz' := hz (mem_range_self d)
    nlinarith

lemma isMeanField_meanField {Q P : Parameter → ℝ} {a : ℝ} (h : IsMeanField Q a P) :
    IsMeanField Q a (meanField Q a) := by
  intro x hx
  simpa only [meanField,(h x hx).csSup_eq (range_nonempty _)] using h x hx

lemma meanField_convex {Q P : Parameter → ℝ} {a : ℝ}
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P) :
    ConvexOn ℝ pressureDomain P := by
  refine ⟨hQ.1,?_⟩
  intro x hx y hy u v hu hv huv
  have hz := hQ.1 hx hy hu hv huv
  apply (hP _ hz).2
  rintro _ ⟨d,rfl⟩
  have hh := hQ.2 (show shiftedField a x d ∈ pressureDomain from hx)
    (show shiftedField a y d ∈ pressureDomain from hy) hu hv huv
  have he : u • shiftedField a x d+v • shiftedField a y d =
      shiftedField a (u • x+v • y) d := by ext <;> dsimp [shiftedField]; ring
  rw [he] at hh
  have h1 := mul_le_mul_of_nonneg_left ((hP x hx).1 (mem_range_self d)) hu
  have h2 := mul_le_mul_of_nonneg_left ((hP y hy).1 (mem_range_self d)) hv
  dsimp [quadraticCost] at *
  nlinarith only [hh,h1,h2]

lemma quadraticCost_continuous {Q : Parameter → ℝ} (hQ : ContinuousOn Q pressureDomain)
    {a : ℝ} {x : Parameter} (hx : x ∈ pressureDomain) :
    Continuous (quadraticCost Q a x) := by
  have hc : Continuous (fun d => Q (shiftedField a x d)) :=
    hQ.comp_continuous (by unfold shiftedField; fun_prop) (fun _ => hx)
  exact hc.sub (by fun_prop)

lemma maximizing_density_eq {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hP : IsMeanField Q a P) {x v : Parameter} (hx : x ∈ pressureDomain) {d : ℝ}
    (hd : quadraticCost Q a x d = P x)
    (hv : SupportOn pressureDomain Q (shiftedField a x d) v) : v.2 = d := by
  have hs := hv (shiftedField a x v.2) hx
  have hb := (hP x hx).1 (mem_range_self v.2)
  have hp : 0 < x.1*a := mul_pos hx ha
  dsimp [quadraticCost,shiftedField,pDot] at hd hs hb
  have he : x.1*a*(v.2-d)^2 ≤ 0 := by nlinarith only [hs,hb,hd]
  have hsq := nonpos_of_mul_nonpos_right he hp
  have hz := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  linarith

lemma lifted_support {Q P : Parameter → ℝ} {a : ℝ}
    (hP : IsMeanField Q a P) {x v : Parameter} (_hx : x ∈ pressureDomain) {d : ℝ}
    (hd : quadraticCost Q a x d = P x) (hvd : v.2 = d)
    (hv : SupportOn pressureDomain Q (shiftedField a x d) v) :
    SupportOn pressureDomain P x (v.1+a*d^2/2,d) := by
  intro y hy
  have hs := hv (shiftedField a y d) hy
  have hb := (hP y hy).1 (mem_range_self d)
  dsimp [quadraticCost,shiftedField,pDot] at *
  rw [hvd] at hs
  nlinarith only [hs,hb,hd]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TransformAttainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

lemma quadratic_bound_attains {f : ℝ → ℝ} (hf : Continuous f) {A B c : ℝ} (hc : 0 < c)
    (hb : ∀ d, f d ≤ A+B*|d|-c*d^2) : ∃ d, ∀ r, f r ≤ f d := by
  let D : ℝ := max 1 (max (2*|B|/c) (2*|A-f 0|/c))
  have hD : 1 ≤ D := le_max_left _ _
  have hDB : 2*|B|/c ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDA : 2*|A-f 0|/c ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hB : 2*|B| ≤ c*D := by have := (div_le_iff₀ hc).mp hDB; linarith
  have hA : 2*|A-f 0| ≤ c*D := by have := (div_le_iff₀ hc).mp hDA; linarith
  have hout (r : ℝ) (hr : D < |r|) : f r ≤ f 0 := by
    have hr1 : 1 ≤ |r| := hD.trans hr.le
    have hb' := hb r
    have hs : |r|^2 = r^2 := sq_abs r
    have hbmul := mul_le_mul_of_nonneg_right hB (abs_nonneg r)
    have hDmul := mul_le_mul_of_nonneg_left hr.le (show 0 ≤ c*|r| by positivity)
    have hDmul' := mul_le_mul_of_nonneg_left hr.le hc.le
    have hrmul := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ c*|r| by positivity)
    have hbm := mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg r)
    have ha := le_abs_self (A-f 0)
    nlinarith
  obtain ⟨d,hd,hmax⟩ := (isCompact_Icc : IsCompact (Icc (-D) D)).exists_isMaxOn
    (show (Icc (-D) D).Nonempty from ⟨0,by constructor <;> linarith⟩) hf.continuousOn
  refine ⟨d,fun r => ?_⟩
  by_cases hr : |r| ≤ D
  · exact hmax (abs_le.mp hr)
  · exact (hout r (lt_of_not_ge hr)).trans (hmax (show (0 : ℝ) ∈ Icc (-D) D by constructor <;> linarith))

lemma quadratic_upper_bound {Q H : ℝ → ℝ} {c b k : ℝ} (hc : 0 < c)
    (hQ : ∀ h, IsLUB ((fun d => h*d-H d) '' Ici 0) (Q h))
    (hH : ∀ d, 0 ≤ d → c*d^2-b*d-k ≤ H d) (h : ℝ) :
    Q h ≤ (h+b)^2/(4*c)+k := by
  apply (hQ h).2
  rintro _ ⟨d,hd,rfl⟩
  have hh := hH d hd
  have hs := sq_nonneg (2*c*d-(h+b))
  have he : ((h+b)^2/(4*c))*(4*c) = (h+b)^2 := by field_simp
  have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ 4*c by positivity)
  nlinarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalMeanField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma isLUB_div_image {f : ℝ → ℝ} {S : Set ℝ} {c z : ℝ}
    (hc : 0 < c) (hz : IsLUB (f '' S) z) :
    IsLUB ((fun d => f d/c) '' S) (z/c) := by
  have hh := hz.mul_right (inv_pos.mpr hc).le
  simpa only [image_image,Function.comp_def,← div_eq_mul_inv] using hh

lemma physicalPressure_isLUB {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B h : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsLUB ((fun d => h*d-physicalCanonical φ t β d) '' Ici 0)
      (physicalPressure φ t (β,h)) := by
  have hh : IsLUB ((fun d => (t*h)*d-canonicalDensity φ β d) '' Ici 0)
      (canonicalPressure φ β (t*h)) :=
    isLUB_csSup (Set.Nonempty.image _ nonempty_Ici)
      (canonicalPressure_bddAbove hφ ht hβ hstable hcore)
  have hh' := isLUB_div_image (lt_trans zero_lt_one ht) hh
  convert hh' using 2
  dsimp [physicalCanonical]
  field_simp
  rfl

lemma physical_meanField {t a : ℝ} (ht : 1 < t) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (hgap : t*a/2 ≤ (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) :
    IsMeanField (physicalPressure (physicalProfile t σ R) t) a
      (fun x => quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)/t) := by
  intro x hx
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hb : x.1*(t*a)/2 ≤ x.1*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) := by
    have := mul_le_mul_of_nonneg_left hgap (le_of_lt hx)
    nlinarith only [this]
  have hp : IsLUB ((fun d => (t*x.2)*d+(x.1*(t*a)/2)*d^2-
      canonicalDensity (physicalProfile t σ R) x.1 d) '' Ici 0)
      (quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)) :=
    isLUB_csSup (Set.Nonempty.image _ nonempty_Ici)
      (quadraticPressure_bddAbove ht (le_of_lt hx) hσ hR hs hsmall hb)
  have hpn := isLUB_div_image ht0 hp
  have hpn' : IsLUB ((fun d => x.2*d+x.1*a*d^2/2-
      physicalCanonical (physicalProfile t σ R) t x.1 d) '' Ici 0)
      (quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)/t) := by
    convert hpn using 2
    dsimp [physicalCanonical]
    field_simp
  exact convolution_isLUB (mul_nonneg (le_of_lt hx) ha)
    (fun h => physicalPressure_isLUB hφ ht (le_of_lt hx) hst hcore (h := h)) hpn'

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MeanFieldAttainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
noncomputable section
namespace ContinuumTemperature

lemma meanField_attained {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ContinuousOn Q pressureDomain) (hP : IsMeanField Q a P)
    {x : Parameter} (hx : x ∈ pressureDomain) {H : ℝ → ℝ}
    (hdual : ∀ h, IsLUB ((fun d => h*d-H d) '' Ici 0) (Q (x.1,h)))
    {c b k : ℝ} (hc : x.1*a/2 < c)
    (hH : ∀ d, 0 ≤ d → c*d^2-b*d-k ≤ H d) :
    ∃ d, quadraticCost Q a x d = P x := by
  have hba : 0 < x.1*a := mul_pos hx ha
  have hc0 : 0 < c := lt_trans (half_pos hba) hc
  let C := x.1*a/2-(x.1*a)^2/(4*c)
  have hC : 0 < C := by
    have he : ((x.1*a)^2/(4*c))*(4*c) = (x.1*a)^2 := by field_simp
    have hp := mul_pos hba (show 0 < 2*c-x.1*a by linarith)
    dsimp [C]
    nlinarith only [he,hp,hc0]
  let A := (x.2+b)^2/(4*c)+k
  let B := |2*(x.2+b)*(x.1*a)/(4*c)|
  have hbound (d : ℝ) : quadraticCost Q a x d ≤ A+B*|d|-C*d^2 := by
    have hu := quadratic_upper_bound hc0 hdual hH (x.2+x.1*a*d)
    have hb := le_abs_self ((2*(x.2+b)*(x.1*a)/(4*c))*d)
    rw [abs_mul] at hb
    have he : (x.2+x.1*a*d+b)^2/(4*c)+k-x.1*a*d^2/2 =
        A+(2*(x.2+b)*(x.1*a)/(4*c))*d-C*d^2 := by dsimp [A,C]; ring
    change Q (x.1,x.2+x.1*a*d)-x.1*a*d^2/2 ≤ _
    calc
      _ ≤ (x.2+x.1*a*d+b)^2/(4*c)+k-x.1*a*d^2/2 := sub_le_sub_right hu _
      _ = _ := he
      _ ≤ _ := by dsimp [B]; linarith only [hb]
  obtain ⟨d,hd⟩ := quadratic_bound_attains (quadraticCost_continuous hQ hx) hC hbound
  refine ⟨d,le_antisymm ((hP x hx).1 (mem_range_self d)) ?_⟩
  apply (hP x hx).2
  rintro _ ⟨r,rfl⟩
  exact hd r

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ActiveSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
noncomputable section
namespace ContinuumTemperature

lemma activeLifts_subset {Q P : Parameter → ℝ} {a : ℝ}
    (hP : IsMeanField Q a P) {x : Parameter} (hx : x ∈ pressureDomain) :
    activeLifts Q a P x ⊆ subgradients pressureDomain P x := by
  intro w hw
  have hh := lifted_support hP hx hw.1 (rfl : (unlift a w).2 = w.2) hw.2
  have he : ((unlift a w).1+a*w.2^2/2,w.2) = w := by
    ext <;> dsimp [unlift]; ring
  rw [he] at hh
  exact hh

lemma activeLifts_nonempty {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P)
    {x : Parameter} (hx : x ∈ pressureDomain)
    (hatt : ∃ d, quadraticCost Q a x d = P x) : (activeLifts Q a P x).Nonempty := by
  obtain ⟨d,hd⟩ := hatt
  obtain ⟨v,hv⟩ := convex_exists_support isOpen_pressureDomain hQ
    (show shiftedField a x d ∈ pressureDomain from hx)
  have he := maximizing_density_eq ha hP hx hd hv
  refine ⟨(v.1+a*d^2/2,d),hd,?_⟩
  convert hv using 1
  ext <;> dsimp [unlift] <;> linarith only [he]

lemma activeLifts_closed_graph {Q P : Parameter → ℝ} {a : ℝ}
    (hQ : ContinuousOn Q pressureDomain) (hP : ContinuousOn P pressureDomain)
    {X V : ℕ → Parameter} {x v : Parameter} (hx : x ∈ pressureDomain)
    (hX : Tendsto X atTop (𝓝 x)) (hV : Tendsto V atTop (𝓝 v))
    (hXS : ∀ n, X n ∈ pressureDomain) (hA : ∀ n, V n ∈ activeLifts Q a P (X n)) :
    v ∈ activeLifts Q a P x := by
  have hshift : Tendsto (fun n => shiftedField a (X n) (V n).2) atTop
      (𝓝 (shiftedField a x v.2)) :=
    (show Continuous (fun p : Parameter × Parameter => shiftedField a p.1 p.2.2) by unfold shiftedField; fun_prop).tendsto
      (x,v) |>.comp (hX.prodMk_nhds hV)
  have hunlift : Tendsto (fun n => unlift a (V n)) atTop (𝓝 (unlift a v)) :=
    (show Continuous (unlift a) by unfold unlift; fun_prop).tendsto v |>.comp hV
  have hQlim : Tendsto (fun n => Q (shiftedField a (X n) (V n).2)) atTop
      (𝓝 (Q (shiftedField a x v.2))) :=
    (hQ (shiftedField a x v.2) (show shiftedField a x v.2 ∈ pressureDomain from hx)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hshift,Eventually.of_forall (fun n => show shiftedField a (X n) (V n).2 ∈ pressureDomain from hXS n)⟩)
  have hPlim := (hP x hx).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hX,Eventually.of_forall hXS⟩)
  have hquad : Tendsto (fun n => (X n).1*a*(V n).2^2/2) atTop (𝓝 (x.1*a*v.2^2/2)) := by
    exact ((((continuous_fst.tendsto x).comp hX).mul_const a).mul (((continuous_snd.tendsto v).comp hV).pow 2)).div_const 2
  constructor
  · exact tendsto_nhds_unique ((hQlim.sub hquad).congr (fun n => (hA n).1)) hPlim
  · exact supportOn_limit hQ (show shiftedField a x v.2 ∈ pressureDomain from hx) hshift hunlift (Eventually.of_forall hXS)
      (Eventually.of_forall fun n => (hA n).2)

lemma meanField_subgradients {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P)
    (hatt : ∀ x ∈ pressureDomain, ∃ d, quadraticCost Q a x d = P x)
    {x : Parameter} (hx : x ∈ pressureDomain) :
    subgradients pressureDomain P x = closedConvexHull ℝ (activeLifts Q a P x) := by
  have hc := meanField_convex hQ hP
  exact support_generators_closedHull isOpen_pressureDomain hc (activeLifts Q a P)
    (fun _ hx => activeLifts_subset hP hx)
    (fun _ hx => activeLifts_nonempty ha hQ hP hx (hatt _ hx))
    (fun hx hX hV hXS hA => activeLifts_closed_graph (hQ.continuousOn isOpen_pressureDomain)
      (hc.continuousOn isOpen_pressureDomain) hx hX hV hXS hA) hx

lemma support_density_nonneg {Q : Parameter → ℝ}
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h))) {x v : Parameter}
    (hx : x ∈ pressureDomain) (hv : SupportOn pressureDomain Q x v) : 0 ≤ v.2 := by
  have hh := hv (x.1,x.2-1) hx
  have hl := hm x.1 hx (show x.2-1 ≤ x.2 by linarith)
  dsimp [pDot] at hh
  simpa only [Prod.mk.eta] using (show 0 ≤ v.2 by linarith)

lemma active_density_nonneg {Q P : Parameter → ℝ} {a : ℝ}
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h))) {x w : Parameter}
    (hx : x ∈ pressureDomain) (hw : w ∈ activeLifts Q a P x) : 0 ≤ w.2 :=
  support_density_nonneg (v := unlift a w) hm (show shiftedField a x w.2 ∈ pressureDomain from hx) hw.2

lemma active_canonical_eq {Q P : Parameter → ℝ} {H : ℝ → ℝ → ℝ} {a : ℝ}
    (hH : IsPartialConjugate Q H)
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h))) {x w : Parameter}
    (hx : x ∈ pressureDomain) (hw : w ∈ activeLifts Q a P x) :
    P x = x.2*w.2+x.1*a*w.2^2/2-H x.1 w.2 := by
  have hd := active_density_nonneg hm hx hw
  have he := fenchel_eq_of_support hH hx hd (supports_iff_supportOn.mpr hw.2)
  have hlow := hw.1
  dsimp [shiftedField,unlift,quadraticCost] at he hlow
  nlinarith only [he,hlow]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma physicalCanonical_quadratic_lower {t β d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (hd : 0 ≤ d) :
    (β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)/t)*d^2-
      (β*t/2)*d-1/t ≤ physicalCanonical (physicalProfile t σ R) t β d := by
  have hh := canonicalDensity_lower_coercive ht hβ hσ hR hs hsmall hd
  have he := entropy_dual_bound 0 hd
  norm_num only [zero_mul,Real.exp_zero,zero_sub] at he
  apply (le_div_iff₀ (lt_trans zero_lt_one ht)).mpr
  have hne : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  field_simp [hne]
  nlinarith only [he,hh]

lemma physical_meanField_attained {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (hgap : t*a/2 < (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)
    {x : Parameter} (hx : x ∈ pressureDomain) :
    ∃ d, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  apply meanField_attained ha (continuousOn_physicalPressure hφ ht hst hcore) hP hx
    (fun h => physicalPressure_isLUB hφ ht (le_of_lt hx) hst hcore (h := h))
    (c := x.1*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)/t)
    (b := x.1*t/2) (k := 1/t)
  · apply (lt_div_iff₀ ht0).mpr
    have hh := mul_lt_mul_of_pos_left hgap hx
    nlinarith only [hh]
  · exact fun d hd => physicalCanonical_quadratic_lower ht (le_of_lt hx) hσ hR hs hsmall hd

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma physical_coefficient_lower {t β m : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hm : 17576*kernelHeight*m ≤ t) :
    β*t/1024 ≤ (β*((t^2/8-2197*t*kernelHeight*m/2)/64)/t) := by
  apply (le_div_iff₀ ht).mpr
  have hh := mul_le_mul_of_nonneg_left hm ht.le
  have hh' : t^2/16 ≤ t^2/8-2197*t*kernelHeight*m/2 := by nlinarith only [hh]
  have hh'' := mul_le_mul_of_nonneg_left hh' hβ
  nlinarith only [hh'']

lemma bounded_density_of_quadratic {t β h a H P d : ℝ}
    (ht : 1 ≤ t) (hβ : 1/4 ≤ β) (hβ' : β ≤ 2) (hh : h ≤ 10)
    (ha : 1024*a ≤ t) (hd : 0 ≤ d) (hP : 0 ≤ P)
    (hH : β*t/1024*d^2-(β*t/2)*d-1/t ≤ H)
    (he : P = h*d+β*a*d^2/2-H) : d ≤ 1048576 := by
  have ht0 : 0 < t := by linarith
  have hc : t/8192 ≤ β*t/1024-β*a/2 := by
    have hh1 := mul_le_mul_of_nonneg_left ha (show 0 ≤ β by linarith)
    have hh2 := mul_le_mul_of_nonneg_right hβ ht0.le
    nlinarith only [hh1,hh2]
  have hlin : h+β*t/2 ≤ 11*t := by
    have hh1 := mul_le_mul_of_nonneg_right hβ' ht0.le
    nlinarith only [hh,hh1,ht]
  have hinv : 1/t ≤ t := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [sq_nonneg (t-1),ht]
  have hh0 := mul_le_mul_of_nonneg_right hc (sq_nonneg d)
  have hh1 := mul_le_mul_of_nonneg_right hlin hd
  have hquad : t*(d^2/8192-11*d-1) ≤ 0 := by nlinarith only [hh0,hh1,hinv,hH,hP,he]
  have hquad' : d^2/8192-11*d-1 ≤ 0 := by
    by_contra hn
    have hh := mul_pos ht0 (lt_of_not_ge hn)
    linarith only [hh,hquad]
  by_contra hn
  have hg : 1048576 < d := lt_of_not_ge hn
  have hh := mul_nonneg hd (le_of_lt (sub_pos.mpr hg))
  nlinarith only [hquad',hg,hh]

lemma meanField_ge_base {Q P : Parameter → ℝ} {a : ℝ}
    (hP : IsMeanField Q a P) {x : Parameter} (hx : x ∈ pressureDomain) : Q x ≤ P x := by
  have hh := (hP x hx).1 (mem_range_self (0:ℝ))
  simpa only [quadraticCost,shiftedField,mul_zero,add_zero,zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero,Prod.mk.eta] using hh

lemma active_pressure_gap {Q P : Parameter → ℝ} {H : ℝ → ℝ → ℝ} {a D : ℝ}
    (hH : IsPartialConjugate Q H)
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h)))
    (hQ : ∀ β, 0 < β → ∀ h, IsLUB ((fun d => h*d-H β d) '' Ici 0) (Q (β,h)))
    {x w : Parameter} (hx : x ∈ pressureDomain) (ha : 0 ≤ a)
    (hw : w ∈ activeLifts Q a P x) (hd : w.2 ≤ D) : P x ≤ Q x+x.1*a*D^2/2 := by
  have hd0 := active_density_nonneg hm hx hw
  have he := active_canonical_eq hH hm hx hw
  have hl := (hQ x.1 hx x.2).1 (mem_image_of_mem (fun d => x.2*d-H x.1 d) hd0)
  have hs : w.2^2 ≤ D^2 := sq_le_sq₀ hd0 (hd0.trans hd) |>.mpr hd
  have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg (le_of_lt hx) ha)
  nlinarith only [he,hl,hmul]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TransformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory Metric
noncomputable section
namespace ContinuumTemperature

lemma strengthened_smallness {t m : ℝ} (ht : 0 < t)
    (hm : 17576*kernelHeight*m ≤ t) :
    2197*t*kernelHeight*m/2 ≤ t^2/8 ∧
    t^2/16 ≤ t^2/8-2197*t*kernelHeight*m/2 := by
  have hh := mul_le_mul_of_nonneg_left hm ht.le
  constructor <;> nlinarith only [hh,sq_nonneg t]

lemma strengthened_gap {t m a : ℝ} (ht : 0 < t)
    (hm : 17576*kernelHeight*m ≤ t) (ha : 1024*a < t) :
    t*a/2 < (t^2/8-2197*t*kernelHeight*m/2)/64 := by
  have hh := (strengthened_smallness ht hm).2
  have hh' := mul_lt_mul_of_pos_left ha ht
  nlinarith only [hh,hh',sq_nonneg t]

lemma physical_transform_active_bound {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t)
    {x w : Parameter} (hβ : 1/4 ≤ x.1) (hβ' : x.1 ≤ 2) (hh : x.2 ≤ 10)
    (hw : w ∈ activeLifts (physicalPressure (physicalProfile t σ R) t) a
      (meanField (physicalPressure (physicalProfile t σ R) t) a) x) :
    0 ≤ w.2 ∧ w.2 ≤ 1048576 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hx : x ∈ pressureDomain := by change 0 < x.1; linarith
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hmono := fun β (hβ : 0 < β) => monotone_physicalPressure hφ ht hβ.le hst hcore
  have hd := active_density_nonneg hmono hx hw
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  have hnon : 0 ≤ meanField (physicalPressure (physicalProfile t σ R) t) a x :=
    le_trans (div_nonneg (canonicalPressure_nonneg hφ ht (le_of_lt hx) hst hcore) ht0.le)
      (meanField_ge_base hP hx)
  have he := active_canonical_eq (physical_partialConjugate hφ ht hst hcore) hmono hx hw
  have hH := physicalCanonical_quadratic_lower ht (le_of_lt hx) hσ hR hs hsmall hd
  have hc := mul_le_mul_of_nonneg_right (physical_coefficient_lower ht0 (le_of_lt hx) hm) (sq_nonneg w.2)
  exact ⟨hd,bounded_density_of_quadratic ht.le hβ hβ' hh hat.le hd hnon (by linarith only [hH,hc]) he⟩

lemma physical_transform_gain {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t)
    {x : Parameter} (hβ : 1/4 ≤ x.1) (hβ' : x.1 ≤ 2) (hh : x.2 ≤ 10) :
    meanField (physicalPressure (physicalProfile t σ R) t) a x ≤
      physicalPressure (physicalProfile t σ R) t x+1048576^2*a := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hx : x ∈ pressureDomain := by change 0 < x.1; linarith
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hmono := fun β (hβ : 0 < β) => monotone_physicalPressure hφ ht hβ.le hst hcore
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  obtain ⟨w,hw⟩ := activeLifts_nonempty ha (convexOn_physicalPressure hφ ht hst hcore) hP hx
    (physical_meanField_attained ht ha hσ hR hs hsmall hgap hx)
  have hd := (physical_transform_active_bound ht ha hσ hR hs hm hat hβ hβ' hh hw).2
  have he := active_pressure_gap (physical_partialConjugate hφ ht hst hcore) hmono
    (fun β hβ h => physicalPressure_isLUB hφ ht hβ.le hst hcore (h := h)) hx ha.le hw hd
  have hh' := mul_le_mul_of_nonneg_right hβ' ha.le
  nlinarith only [he,hh']

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CompactHulls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology
open Set
namespace ContinuumTemperature

lemma isCompact_convexJoin {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {S T : Set E} (hS : IsCompact S) (hT : IsCompact T) :
    IsCompact (convexJoin ℝ S T) := by
  have he : convexJoin ℝ S T =
      (fun p : ℝ × E × E => (1-p.1) • p.2.1+p.1 • p.2.2) '' (Icc (0:ℝ) 1 ×ˢ S ×ˢ T) := by
    ext z
    simp only [mem_convexJoin,segment_eq_image,mem_image,mem_prod,Prod.exists]
    constructor
    · rintro ⟨x,hx,y,hy,c,hc,rfl⟩
      exact ⟨c,x,y,⟨hc,hx,hy⟩,rfl⟩
    · rintro ⟨c,x,y,⟨hc,hx,hy⟩,rfl⟩
      exact ⟨x,hx,y,hy,c,hc,rfl⟩
  rw [he]
  exact (isCompact_Icc.prod (hS.prod hT)).image (by fun_prop)

lemma compact_convexHull_union {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {S T : Set E} (hS : IsCompact S) (hT : IsCompact T)
    (hcS : Convex ℝ S) (hcT : Convex ℝ T) : IsCompact (convexHull ℝ (S ∪ T)) := by
  by_cases hs : S.Nonempty
  · by_cases ht : T.Nonempty
    · rw [hcS.convexHull_union hcT hs ht]
      exact isCompact_convexJoin hS hT
    · rw [not_nonempty_iff_eq_empty.mp ht,union_empty,hcS.convexHull_eq]
      exact hS
  · rw [not_nonempty_iff_eq_empty.mp hs,empty_union,hcT.convexHull_eq]
    exact hT

lemma compact_convexHull_iUnion_fin {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {n : ℕ} (K : Fin n → Set E) (hk : ∀ i, IsCompact (K i)) (hc : ∀ i, Convex ℝ (K i)) :
    IsCompact (convexHull ℝ (⋃ i, K i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ,← convexHull_convexHull_union_right]
    exact compact_convexHull_union (hk 0) (ih _ (fun i => hk i.succ) (fun i => hc i.succ))
      (hc 0) (convex_convexHull _ _)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TriangleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma triangleWeight_sum (w : Fin 3 → Parameter) (z : Parameter) :
    ∑ i, triangleWeight w z i = 1 := by
  simp [Fin.sum_univ_succ,triangleWeight]

lemma triangleWeight_combination {w : Fin 3 → Parameter} (hD : triangleDet w ≠ 0)
    (z : Parameter) : ∑ i, triangleWeight w z i • w i = z := by
  ext
  all_goals
    simp only [Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    simp [Fin.sum_univ_succ,triangleWeight]
    field_simp
    dsimp [triangleDet] at hD ⊢
    field_simp at *
    ring

lemma triangle_mem_of_weights {w : Fin 3 → Parameter} (hD : triangleDet w ≠ 0)
    {z : Parameter} (hz : ∀ i, 0 ≤ triangleWeight w z i) : z ∈ convexHull ℝ (range w) := by
  rw [← triangleWeight_combination hD z]
  exact (convex_convexHull ℝ (range w)).sum_mem (fun i _ => hz i)
    (triangleWeight_sum w z) (fun i _ => subset_convexHull ℝ _ (mem_range_self i))

lemma triangleDet_vertex {p : ℝ} (hp : 0 < p) : triangleDet (triangleVertex p) ≠ 0 := by
  have he : triangleDet (triangleVertex p) = -9*p^2 := by norm_num [triangleDet,triangleVertex,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]; ring
  rw [he]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne')

lemma triangleWeight_center {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    triangleWeight (triangleVertex p) (triangleCenter p) i = 1/3 := by
  fin_cases i <;> norm_num [triangleWeight,triangleVertex,triangleCenter,triangleDet,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
  all_goals field_simp [hp.ne']; ring

lemma continuous_triangleDet : Continuous triangleDet := by unfold triangleDet; fun_prop

lemma continuousAt_triangleWeight {w : Fin 3 → Parameter} {z : Parameter}
    (hD : triangleDet w ≠ 0) (i : Fin 3) :
    ContinuousAt (fun q : (Fin 3 → Parameter) × Parameter => triangleWeight q.1 q.2 i) (w,z) := by
  have hc := continuous_triangleDet
  unfold triangleWeight
  split_ifs <;> fun_prop (disch := exact hD)

lemma robust_vertex_triangle {p : ℝ} (hp : 0 < p) :
    ∃ τ γ : ℝ, 0 < τ ∧ 0 < γ ∧
      ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
        closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w) := by
  let v := triangleVertex p
  let g := triangleCenter p
  have hD : triangleDet v ≠ 0 := triangleDet_vertex hp
  have hne : ∀ᶠ q : (Fin 3 → Parameter) × Parameter in 𝓝 (v,g), triangleDet q.1 ≠ 0 :=
    (continuous_triangleDet.continuousAt.comp continuousAt_fst).eventually_ne hD
  have hpos : ∀ᶠ q : (Fin 3 → Parameter) × Parameter in 𝓝 (v,g), ∀ i, 0 < triangleWeight q.1 q.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_triangleWeight (z := g) hD i).eventually (Ioi_mem_nhds (by change 0 < triangleWeight (triangleVertex p) (triangleCenter p) i; rw [triangleWeight_center hp]; norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hne.and hpos)
  refine ⟨δ/2,δ/2,by positivity,by positivity,?_⟩
  intro w hw z hz
  have hd : dist (w,z) (v,g) < δ := by
    rw [Prod.dist_eq,max_lt_iff]
    constructor
    · exact lt_of_le_of_lt ((dist_pi_le_iff (by positivity : 0 ≤ δ/2)).mpr hw) (by linarith)
    · exact lt_of_le_of_lt hz (by linarith)
  have hh := hball hd
  exact triangle_mem_of_weights hh.1 (fun i => (hh.2 i).le)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem isPacking_zero (L : ℝ) : IsPacking L 0 := by
  refine ⟨Fin.elim0, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

theorem packing_card_cubeCells {ι : Type u_1} [Fintype ι] {L : ℝ}
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) : Fintype.card ι ≤ (cubeCells L).card := by
  let f : ι → {k // k ∈ cubeCells L} := fun i =>
    ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hh := dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij)
    exact (not_lt_of_ge (hsep i j hne)) hh
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem IsPacking.card_bound {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ (cubeCells L).card := by
  obtain ⟨x,hx,hs⟩ := h
  simpa only [Fintype.card_fin] using packing_card_cubeCells x hx hs

theorem packingNumber_realized (L : ℝ) : IsPacking L (packingNumber L) := by
  exact Nat.findGreatest_spec (show 0 ≤ (cubeCells L).card from Nat.zero_le _)
    (isPacking_zero L)

theorem IsPacking.le_packingNumber {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ packingNumber L := by
  exact Nat.le_findGreatest h.card_bound h

theorem packingNumber_bound {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ) ≤ (4*L+2)^3 :=
  (Nat.cast_le.mpr (packingNumber_realized L).card_bound).trans (card_cubeCells_le hL)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem familyTerm_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) (n : ℕ) :
    familyTerm (fun ι _ x => c*F ι x) A n = c*familyTerm F A n := by
  unfold familyTerm familyIntegral
  rw [integral_const_mul]
  ring

theorem familyTerm_add (F G : ConfigFamily) (A : Set Space) (n : ℕ)
    (hFi : IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A}) :
    familyTerm (fun ι _ x => F ι x+G ι x) A n = familyTerm F A n+familyTerm G A n := by
  unfold familyTerm familyIntegral
  rw [integral_add hFi hGi, add_div]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem GrandFinite.const_mul {F : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (c : ℝ) : GrandFinite (fun ι _ x => c*F ι x) D where
  integrable := fun ι _ => (hF.integrable ι).const_mul c
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => c*F ι x) D n)
    simp_rw [familyTerm_const_mul]
    exact hF.summable.mul_left c

theorem GrandFinite.add {F G : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (hG : GrandFinite G D) :
    GrandFinite (fun ι _ x => F ι x+G ι x) D where
  integrable := fun ι _ => (hF.integrable ι).add (hG.integrable ι)
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => F ι x+G ι x) D n)
    simp_rw [familyTerm_add F G D _ (hF.integrable _) (hG.integrable _)]
    exact hF.summable.add hG.summable

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem packing_fractions_bddAbove :
    BddAbove ((fun L : ℝ => (packingNumber L : ℝ)/(L+2)^3) '' Ici 0) := by
  refine ⟨64, ?_⟩
  rintro _ ⟨L,hL,rfl⟩
  change 0 ≤ L at hL
  apply (div_le_iff₀ (pow_pos (by linarith : 0 < L+2) 3)).2
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 4*L+2)
    (by linarith : 4*L+2 ≤ 4*(L+2)) 3
  have hp := packingNumber_bound hL
  nlinarith only [hp,hh]

theorem packing_fraction_le {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ)/(L+2)^3 ≤ packingDensity :=
  le_csSup packing_fractions_bddAbove ⟨L,hL,rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have hp : IsPacking 0 1 := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i j; simp
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  have hn : (1 : ℝ) ≤ packingNumber 0 := by exact_mod_cast hp.le_packingNumber
  have hh := packing_fraction_le (L := 0) (le_refl 0)
  norm_num at hh
  linarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.AppendAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem summable_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) : Summable (prepend a σ) := by
  exact (summable_nat_add_iff 1).mp hs

theorem tsum_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) :
    ∑' n, prepend a σ n = a+∑' n, σ n := by
  exact (summable_prepend a hs).tsum_eq_zero_add

theorem prepend_nonneg {a : ℝ} {σ : ℕ → ℝ} (ha : 0 ≤ a) (hσ : ∀ n, 0 ≤ σ n) :
    ∀ n, 0 ≤ prepend a σ n
  | 0 => ha
  | n+1 => hσ n

theorem prepend_ge_one {a : ℝ} {σ : ℕ → ℝ} (ha : 1 ≤ a) (hσ : ∀ n, 1 ≤ σ n) :
    ∀ n, 1 ≤ prepend a σ n
  | 0 => ha
  | n+1 => hσ n

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma threeCore_convex (p : ℝ) : ConvexOn ℝ pressureDomain (threeCore p) := by
  have hdom : Convex ℝ pressureDomain := by
    change Convex ℝ {x : Parameter | 0 < x.1}
    exact (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  apply (convexOn_const (0 : ℝ) hdom).sup
  apply ConvexOn.sup
  · refine ⟨hdom,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp
    nlinarith
  · refine ⟨hdom,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp
    have hh := congrArg (fun z : ℝ => z*(9*p)) hab
    nlinarith only [hh]

lemma three_meanField {p a : ℝ} (ha : 0 ≤ a) : IsMeanField (threeCore p) a (threeMeanField p a) := by
  intro x hx
  have hcoef : 0 ≤ x.1*a := mul_nonneg (le_of_lt hx) ha
  have h0 : ∀ d : ℝ, -(x.1*a*d^2/2) ≤ 0 := fun d => neg_nonpos.mpr (div_nonneg (mul_nonneg hcoef (sq_nonneg d)) (by norm_num))
  have h1 : ∀ d : ℝ, p*(x.2+x.1*a*d)-x.1*a*d^2/2 ≤ p*x.2+x.1*a*p^2/2 := by
    intro d
    have hh := mul_nonneg hcoef (sq_nonneg (d-p))
    nlinarith only [hh]
  have h2 : ∀ d : ℝ, 4*p*(x.2+x.1*a*d)-9*p-x.1*a*d^2/2 ≤ 4*p*x.2-9*p+x.1*a*(4*p)^2/2 := by
    intro d
    have hh := mul_nonneg hcoef (sq_nonneg (d-4*p))
    nlinarith only [hh]
  constructor
  · rintro _ ⟨d,rfl⟩
    change max 0 (max (p*(x.2+x.1*a*d)) (4*p*(x.2+x.1*a*d)-9*p))-x.1*a*d^2/2 ≤ _
    rw [← max_sub_sub_right,← max_sub_sub_right]
    apply max_le
    · exact (show 0-x.1*a*d^2/2 ≤ 0 by simpa using h0 d).trans (le_max_left _ _)
    · apply max_le
      · exact (h1 d).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (h2 d).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro b hb
    have he0 := hb (mem_range_self (0:ℝ))
    have he1 := hb (mem_range_self p)
    have he2 := hb (mem_range_self (4*p))
    have hl0 : 0 ≤ quadraticCost (threeCore p) a x 0 := by
      simp only [quadraticCost,shiftedField,mul_zero,add_zero,zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero,threeCore]
      exact le_max_left _ _
    have hl1 : p*x.2+x.1*a*p^2/2 ≤ quadraticCost (threeCore p) a x p := by
      have hh := (le_max_left (p*(x.2+x.1*a*p)) (4*p*(x.2+x.1*a*p)-9*p)).trans (le_max_right (0:ℝ) _)
      dsimp [quadraticCost,shiftedField,threeCore]
      nlinarith only [hh]
    have hl2 : 4*p*x.2-9*p+x.1*a*(4*p)^2/2 ≤ quadraticCost (threeCore p) a x (4*p) := by
      have hh := (le_max_right (p*(x.2+x.1*a*(4*p))) (4*p*(x.2+x.1*a*(4*p))-9*p)).trans (le_max_right (0:ℝ) _)
      dsimp [quadraticCost,shiftedField,threeCore]
      nlinarith only [hh]
    exact max_le (hl0.trans he0) (max_le (hl1.trans he1) (hl2.trans he2))

lemma support_first_zero {f : ℝ → ℝ} {x w : Parameter} (hx : x ∈ pressureDomain)
    (hw : SupportOn pressureDomain (fun y => f y.2) x w) : w.1=0 := by
  change 0 < x.1 at hx
  have h1 := hw (2*x.1,x.2) (by change 0 < 2*x.1; positivity)
  have h2 := hw (x.1/2,x.2) (by change 0 < x.1/2; positivity)
  dsimp [pDot] at h1 h2
  nlinarith [hx]

lemma firstMass_pos {p : ℝ} (hp : 0 < p) : 0 < firstMass p := by unfold firstMass; positivity
lemma firstMass_mul {p : ℝ} (hp : 0 < p) : firstMass p*p = 3/2 := by
  unfold firstMass
  field_simp

lemma threeMeanField_initial {p : ℝ} (hp : 0 < p) : threeMeanField p (firstMass p) initialPoint=0 := by
  have hh := firstMass_mul hp
  have hh2 : firstMass p*p^2=3*p/2 := by linear_combination p*hh
  have h1 : p*(-3/4)+firstMass p*p^2/2=0 := by nlinarith only [hh2]
  have h2 : 4*p*(-3/4)-9*p+firstMass p*(4*p)^2/2=0 := by nlinarith only [hh2]
  simp only [threeMeanField,initialPoint,one_mul,h1,h2,max_self]

lemma three_active_initial {p : ℝ} (hp : 0 < p) :
    activeLifts (threeCore p) (firstMass p) (threeMeanField p (firstMass p)) initialPoint ⊆ range (triangleVertex p) := by
  intro w hw
  have hβ : initialPoint ∈ pressureDomain := by norm_num [initialPoint,pressureDomain]
  have he := support_first_zero (f := fun h => max 0 (max (p*h) (4*p*h-9*p))) (show shiftedField (firstMass p) initialPoint w.2 ∈ pressureDomain from hβ) hw.2
  have hc := hw.1
  rw [threeMeanField_initial hp] at hc
  have ha := firstMass_pos hp
  have hap := firstMass_mul hp
  have hap2 : firstMass p*p^2=3*p/2 := by linear_combination p*hap
  have hapd : firstMass p*p*w.2=3*w.2/2 := by linear_combination w.2*hap
  change w.1-firstMass p*w.2^2/2=0 at he
  simp only [quadraticCost,threeCore,shiftedField,initialPoint,one_mul] at hc
  change max 0 (max (p*(-3/4+firstMass p*w.2)) (4*p*(-3/4+firstMass p*w.2)-9*p))-firstMass p*w.2^2/2=0 at hc
  rcases le_total 0 (max (p*(-3/4+firstMass p*w.2)) (4*p*(-3/4+firstMass p*w.2)-9*p)) with h | h
  · rw [max_eq_right h] at hc
    rcases le_total (p*(-3/4+firstMass p*w.2)) (4*p*(-3/4+firstMass p*w.2)-9*p) with hh | hh
    · rw [max_eq_right hh] at hc
      have hd : w.2=4*p := by
        have hh1 : firstMass p*(w.2-4*p)^2=0 := by nlinarith only [hc,hap2,hapd]
        have := (mul_eq_zero.mp hh1).resolve_left ha.ne'
        nlinarith [sq_nonneg (w.2-4*p)]
      refine ⟨2,?_⟩
      ext <;> norm_num [triangleVertex,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
      · rw [hd] at he; nlinarith only [he,hap2]
      · exact hd.symm
    · rw [max_eq_left hh] at hc
      have hd : w.2=p := by
        have hh1 : firstMass p*(w.2-p)^2=0 := by nlinarith only [hc,hap2,hapd]
        have := (mul_eq_zero.mp hh1).resolve_left ha.ne'
        nlinarith [sq_nonneg (w.2-p)]
      refine ⟨1,?_⟩
      ext <;> norm_num [triangleVertex]
      · rw [hd] at he; nlinarith only [he,hap2]
      · exact hd.symm
  · rw [max_eq_left h] at hc
    have hd : w.2=0 := by
      have hm : firstMass p*w.2^2=0 := by linarith only [hc]
      have hs := (mul_eq_zero.mp hm).resolve_left ha.ne'
      nlinarith [sq_nonneg w.2]
    refine ⟨0,?_⟩
    ext <;> norm_num [triangleVertex]
    · rw [hd] at he; simpa using he.symm
    · exact hd.symm

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TriangleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma vertexCoordinate_center {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    vertexCoordinate p (triangleCenter p) i = 1/3 := by
  fin_cases i <;> norm_num [vertexCoordinate,triangleCenter]
  all_goals field_simp [hp.ne']; ring

lemma vertexCoordinate_affine (p a b : ℝ) (hab : a+b=1) (x y : Parameter) (i : Fin 3) :
    vertexCoordinate p (a • x+b • y) i = a*vertexCoordinate p x i+b*vertexCoordinate p y i := by
  fin_cases i <;> simp [vertexCoordinate]
  · linear_combination -hab
  · ring
  · ring

lemma vertex_halfspace_convex (p c : ℝ) (i : Fin 3) :
    Convex ℝ {z | vertexCoordinate p z i ≤ c} := by
  intro x hx y hy a b ha hb hab
  change vertexCoordinate p (a • x+b • y) i ≤ c
  rw [vertexCoordinate_affine p a b hab]
  exact (add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)).trans_eq (by rw [← add_mul,hab,one_mul])

lemma coordinates_of_near_vertex {p τ : ℝ} {i : Fin 3} {w : Parameter}
    (hw : w ∈ closedBall (triangleVertex p i) τ) :
    |w.1-(triangleVertex p i).1| ≤ τ ∧ |w.2-(triangleVertex p i).2| ≤ τ := by
  simpa only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    Real.norm_eq_abs,max_le_iff] using hw

lemma vertexCoordinate_near_other {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    {i j : Fin 3} (hij : i ≠ j) {w : Parameter}
    (hw : w ∈ closedBall (triangleVertex p j) τ) : vertexCoordinate p w i ≤ 1/6 := by
  obtain ⟨h1,h2⟩ := coordinates_of_near_vertex hw
  obtain ⟨hl1,hu1⟩ := abs_le.mp h1
  obtain ⟨hl2,hu2⟩ := abs_le.mp h2
  apply (mul_le_mul_iff_right₀ hp).mp
  fin_cases i <;> fin_cases j <;> norm_num [vertexCoordinate,triangleVertex] at hl1 hu1 hl2 hu2 ⊢
  all_goals try contradiction
  all_goals field_simp [hp.ne']; nlinarith only [hl1,hu1,hl2,hu2,hτ,hp]

lemma vertex_density_separation {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (Prod.snd '' closedBall (triangleVertex p i) τ)
      (Prod.snd '' closedBall (triangleVertex p j) τ) := by
  apply Set.disjoint_left.mpr
  rintro d ⟨w,hw,rfl⟩ ⟨z,hz,he⟩
  have hw' := (coordinates_of_near_vertex hw).2
  have hz' := (coordinates_of_near_vertex hz).2
  obtain ⟨hw1,hw2⟩ := abs_le.mp hw'
  obtain ⟨hz1,hz2⟩ := abs_le.mp hz'
  fin_cases i <;> fin_cases j <;> norm_num [triangleVertex] at hw1 hw2 hz1 hz2
  all_goals try contradiction
  all_goals linarith only [hw1,hw2,hz1,hz2,he,hτ,hp]

lemma all_vertex_groups_nonempty {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    (K : Fin 3 → Set Parameter) (hk : ∀ i, K i ⊆ closedBall (triangleVertex p i) τ)
    (hg : triangleCenter p ∈ convexHull ℝ (⋃ i, K i)) : ∀ i, (K i).Nonempty := by
  intro i
  by_contra hn
  have hs : (⋃ j, K j) ⊆ {z | vertexCoordinate p z i ≤ 1/6} := by
    rintro z ⟨_,⟨j,rfl⟩,hz⟩
    have hji : i ≠ j := by intro he; subst j; exact hn ⟨z,hz⟩
    exact vertexCoordinate_near_other hp hτ hji (hk j hz)
  have hh := convexHull_min hs (vertex_halfspace_convex p (1/6) i) hg
  change vertexCoordinate p (triangleCenter p) i ≤ 1/6 at hh
  rw [vertexCoordinate_center hp] at hh
  norm_num at hh

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Regroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma slopeGroups_compact (P : Parameter → ℝ) (x : Parameter) (v : Fin 3 → Parameter) (τ : ℝ) (i : Fin 3) :
    IsCompact (slopeGroups P x v τ i) :=
  (isCompact_closedBall _ _).of_isClosed_subset
    ((subgradients_closed _ _ _).inter isClosed_closedBall) inter_subset_right

lemma slopeGroups_convex (P : Parameter → ℝ) (x : Parameter) (v : Fin 3 → Parameter) (τ : ℝ) (i : Fin 3) :
    Convex ℝ (slopeGroups P x v τ i) :=
  (subgradients_convex _ _ _).inter (convex_closedBall _ _)

lemma regroup_active {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P)
    (hatt : ∀ y ∈ pressureDomain, ∃ d, quadraticCost Q a y d = P y)
    {x : Parameter} (hx : x ∈ pressureDomain) {v : Fin 3 → Parameter} {τ : ℝ}
    (hA : activeLifts Q a P x ⊆ ⋃ i, closedBall (v i) τ) :
    subgradients pressureDomain P x = convexHull ℝ (⋃ i, slopeGroups P x v τ i) := by
  let K := slopeGroups P x v τ
  have hKc := compact_convexHull_iUnion_fin K (slopeGroups_compact P x v τ) (slopeGroups_convex P x v τ)
  apply Subset.antisymm
  · rw [meanField_subgradients ha hQ hP hatt hx]
    apply closedConvexHull_min _ (convex_convexHull _ _) hKc.isClosed
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hA hw)
    exact subset_convexHull ℝ _ (mem_iUnion.mpr ⟨i,activeLifts_subset hP hx hw,hi⟩)
  · apply convexHull_min _ (subgradients_convex _ _ _)
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp hw
    exact hi.1

lemma support_ball_of_vertex_groups {P : Parameter → ℝ} {x : Parameter} {p τ γ : ℝ}
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    {K : Fin 3 → Set Parameter} (hne : ∀ i, (K i).Nonempty)
    (hK : ∀ i, K i ⊆ closedBall (triangleVertex p i) τ)
    (he : subgradients pressureDomain P x = convexHull ℝ (⋃ i, K i)) :
    closedBall (triangleCenter p) γ ⊆ subgradients pressureDomain P x := by
  choose w hw using hne
  rw [he]
  exact (hgeom w (fun i => hK i (hw i))).trans (convexHull_mono (range_subset_iff.mpr fun i => mem_iUnion.mpr ⟨i,hw i⟩))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.IdealSlopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma three_vertex_support {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    SupportOn pressureDomain (threeMeanField p (firstMass p)) initialPoint (triangleVertex p i) := by
  intro y hy
  rw [threeMeanField_initial hp]
  have hap := firstMass_mul hp
  have hap2 : firstMass p*p^2=3*p/2 := by linear_combination p*hap
  have hap2y := congrArg (fun z : ℝ => y.1*z) hap2
  have h0 : 0 ≤ threeMeanField p (firstMass p) y := le_max_left _ _
  have h1 : p*y.2+y.1*firstMass p*p^2/2 ≤ threeMeanField p (firstMass p) y :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2 : 4*p*y.2-9*p+y.1*firstMass p*(4*p)^2/2 ≤ threeMeanField p (firstMass p) y :=
    (le_max_right _ _).trans (le_max_right _ _)
  fin_cases i <;> norm_num [triangleVertex,initialPoint,pDot,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
  · exact h0
  · nlinarith only [h1,hap2y]
  · nlinarith only [h2,hap2y]

lemma three_support_contains_triangle {p : ℝ} (hp : 0 < p) :
    convexHull ℝ (range (triangleVertex p)) ⊆ subgradients pressureDomain (threeMeanField p (firstMass p)) initialPoint :=
  convexHull_min (range_subset_iff.mpr (three_vertex_support hp)) (subgradients_convex _ _ _)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConvolutionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma locallyUniform_reindex {ι : Type u_1} {κ : Type u_2} {l : Filter ι} {k : Filter κ}
    {Q : ι → Parameter → ℝ} {q : Parameter → ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q l pressureDomain)
    {θ : κ → ι} (hθ : Tendsto θ k l) :
    TendstoLocallyUniformlyOn (fun n => Q (θ n)) q k pressureDomain := by
  intro u hu x hx
  obtain ⟨t,ht,h⟩ := hQ u hu x hx
  exact ⟨t,ht,hθ.eventually h⟩

lemma quadraticCost_tendsto {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain)
    (hq : ContinuousOn q pressureDomain)
    {a d : ℕ → ℝ} {a₀ d₀ : ℝ} (ha : Tendsto a atTop (𝓝 a₀))
    (hd : Tendsto d atTop (𝓝 d₀)) {X : ℕ → Parameter} {x : Parameter}
    (hx : x ∈ pressureDomain) (hX : Tendsto X atTop (𝓝 x)) :
    Tendsto (fun n => quadraticCost (Q n) (a n) (X n) (d n)) atTop
      (𝓝 (quadraticCost q a₀ x d₀)) := by
  have hX1 := (continuous_fst.tendsto x).comp hX
  have hX2 := (continuous_snd.tendsto x).comp hX
  have hf : Tendsto (fun n => shiftedField (a n) (X n) (d n)) atTop
      (𝓝 (shiftedField a₀ x d₀)) :=
    hX1.prodMk_nhds (hX2.add ((hX1.mul ha).mul hd))
  have he : ∀ᶠ n in atTop, shiftedField (a n) (X n) (d n) ∈ pressureDomain :=
    (hX.eventually (isOpen_pressureDomain.mem_nhds hx))
  have hval := hQ.tendsto_comp (hq _ (show shiftedField a₀ x d₀ ∈ pressureDomain from hx))
    (show shiftedField a₀ x d₀ ∈ pressureDomain from hx) (tendsto_nhdsWithin_iff.2 ⟨hf,he⟩)
  exact hval.sub (((hX1.mul ha).mul (hd.pow 2)).div_const 2)

lemma meanField_tendsto_of_bounded_maximizers {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    {P : ℕ → Parameter → ℝ} {p : Parameter → ℝ} {a : ℕ → ℝ} {a₀ : ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain) (hq : ContinuousOn q pressureDomain)
    (ha : Tendsto a atTop (𝓝 a₀)) (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    (hp : IsMeanField q a₀ p) {X : ℕ → Parameter} {x : Parameter}
    (hx : x ∈ pressureDomain) (hX : Tendsto X atTop (𝓝 x))
    (hXS : ∀ n, X n ∈ pressureDomain) {D : ℝ}
    (hatt : ∀ n, ∃ d ∈ Icc 0 D, quadraticCost (Q n) (a n) (X n) d = P n (X n)) :
    Tendsto (fun n => P n (X n)) atTop (𝓝 (p x)) := by
  choose d hd he using hatt
  apply metric_tendsto_of_subseq
  intro φ hφ
  obtain ⟨r,_,ψ,hψ,hr⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) D)).tendsto_subseq
    (fun n => hd (φ n))
  let θ := φ ∘ ψ
  have hθ := (hφ.comp hψ).tendsto_atTop
  have hlim := quadraticCost_tendsto (locallyUniform_reindex hQ hθ) hq (ha.comp hθ) hr hx (hX.comp hθ)
  have hle : quadraticCost q a₀ x r ≤ p x := (hp x hx).1 (mem_range_self r)
  have hge : p x ≤ quadraticCost q a₀ x r := by
    apply (hp x hx).2
    rintro _ ⟨s,rfl⟩
    have hs := quadraticCost_tendsto (locallyUniform_reindex hQ hθ) hq (ha.comp hθ)
      (tendsto_const_nhds (x := s)) hx (hX.comp hθ)
    apply le_of_tendsto_of_tendsto hs hlim
    exact Eventually.of_forall fun n => by
      change quadraticCost (Q (θ n)) (a (θ n)) (X (θ n)) s ≤
        quadraticCost (Q (θ n)) (a (θ n)) (X (θ n)) (d (θ n))
      rw [he]
      exact (hP (θ n) _ (hXS (θ n))).1 (mem_range_self s)
  have heq := le_antisymm hle hge
  refine ⟨ψ,hψ,?_⟩
  rw [heq] at hlim
  exact hlim.congr (fun n => he (θ n))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ActiveLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma active_subseq_of_density_bound {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    {P : ℕ → Parameter → ℝ} {p : Parameter → ℝ} {a : ℕ → ℝ} {a₀ : ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain)
    (hconv : ∀ n, ConvexOn ℝ pressureDomain (Q n)) (hq : ContinuousOn q pressureDomain)
    (ha : Tendsto a atTop (𝓝 a₀)) (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    (hp : IsMeanField q a₀ p) {X W : ℕ → Parameter} {x : Parameter}
    (hx : x ∈ pressureDomain) (hX : Tendsto X atTop (𝓝 x)) (hXS : ∀ n, X n ∈ pressureDomain)
    (hA : ∀ n, W n ∈ activeLifts (Q n) (a n) (P n) (X n))
    {D : ℝ} (hD : ∀ n, (W n).2 ∈ Icc 0 D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w ∈ activeLifts q a₀ p x,
      Tendsto (W ∘ φ) atTop (𝓝 w) := by
  obtain ⟨d,_,φ,hφ,hd⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) D)).tendsto_subseq hD
  let V : ℕ → Parameter := fun n => unlift (a (φ n)) (W (φ n))
  let Y : ℕ → Parameter := fun n => shiftedField (a (φ n)) (X (φ n)) (W (φ n)).2
  let y := shiftedField a₀ x d
  have hy : y ∈ pressureDomain := hx
  have hXφ := hX.comp hφ.tendsto_atTop
  have haφ := ha.comp hφ.tendsto_atTop
  have hY : Tendsto Y atTop (𝓝 y) := by
    have hh := ((continuous_fst.tendsto x).comp hXφ).prodMk_nhds
      (((continuous_snd.tendsto x).comp hXφ).add
        ((((continuous_fst.tendsto x).comp hXφ).mul haφ).mul hd))
    simpa only [Y,y,shiftedField,Function.comp_def] using hh
  obtain ⟨C,hC⟩ := eventually_subgradients_bounded isOpen_pressureDomain
    (Eventually.of_forall fun n => hconv (φ n))
    (fun z hz => (hQ.tendsto_at hz).comp hφ.tendsto_atTop) hy hY
  have hVC : ∀ᶠ n in atTop, V n ∈ closedBall 0 C := by
    filter_upwards [hC] with n hn
    simpa only [mem_closedBall,dist_zero_right] using hn _ (hA (φ n)).2
  obtain ⟨v,_,ψ,hψ,hv⟩ := (isCompact_closedBall (0 : Parameter) C).tendsto_subseq' hVC.frequently
  let θ := φ ∘ ψ
  have hθ := (hφ.comp hψ).tendsto_atTop
  let w : Parameter := (v.1+a₀*v.2^2/2,v.2)
  have hV2 := (continuous_snd.tendsto v).comp hv
  have hW : Tendsto (W ∘ θ) atTop (𝓝 w) := by
    have hh := (((continuous_fst.tendsto v).comp hv).add
      (((ha.comp hθ).mul (hV2.pow 2)).div_const 2)).prodMk_nhds hV2
    simpa only [V,unlift,w,θ,Function.comp_def,sub_add_cancel,Prod.mk.eta] using hh
  have hxl := hX.comp hθ
  have hwl := (continuous_snd.tendsto w).comp hW
  have hpl := meanField_tendsto_of_bounded_maximizers (locallyUniform_reindex hQ hθ) hq
    (ha.comp hθ) (fun n => hP (θ n)) hp hx hxl (fun n => hXS (θ n))
    (fun n => ⟨(W (θ n)).2,hD (θ n),(hA (θ n)).1⟩)
  have hcost := quadraticCost_tendsto (locallyUniform_reindex hQ hθ) hq (ha.comp hθ) hwl hx hxl
  have hshift : Tendsto (fun n => shiftedField (a (θ n)) (X (θ n)) (W (θ n)).2) atTop
      (𝓝 (shiftedField a₀ x w.2)) :=
    ((continuous_fst.tendsto x).comp hxl).prodMk_nhds
      (((continuous_snd.tendsto x).comp hxl).add
        ((((continuous_fst.tendsto x).comp hxl).mul (ha.comp hθ)).mul hwl))
  have hunlift : Tendsto (fun n => unlift (a (θ n)) (W (θ n))) atTop (𝓝 (unlift a₀ w)) := by
    exact (((continuous_fst.tendsto w).comp hW).sub
      (((ha.comp hθ).mul (hwl.pow 2)).div_const 2)).prodMk_nhds hwl
  refine ⟨θ,hφ.comp hψ,w,⟨?_,?_⟩,hW⟩
  · exact tendsto_nhds_unique (hcost.congr (fun n => (hA (θ n)).1)) hpl
  · exact supportOn_varying_limit isOpen_pressureDomain (locallyUniform_reindex hQ hθ) hq
      (show shiftedField a₀ x w.2 ∈ pressureDomain from hx) hshift hunlift (Eventually.of_forall fun n => (hA (θ n)).2)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ActiveUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma active_uniform_near {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    {P : ℕ → Parameter → ℝ} {p : Parameter → ℝ} {a : ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain)
    (hconv : ∀ n, ConvexOn ℝ pressureDomain (Q n)) (hq : ContinuousOn q pressureDomain)
    (hP : ∀ n, IsMeanField (Q n) a (P n)) (hp : IsMeanField q a p)
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain) {D : ℝ}
    (hD : ∀ n, ∀ y ∈ ball x r, ∀ w ∈ activeLifts (Q n) a (P n) y, w.2 ∈ Icc 0 D)
    {U : Set Parameter} (hU : IsOpen U) (hAU : activeLifts q a p x ⊆ U) :
    ∃ δ > 0, δ < r ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x δ, activeLifts (Q n) a (P n) y ⊆ U := by
  by_contra hn
  push Not at hn
  have hex : ∀ m : ℕ, ∃ n ≥ m, ∃ y ∈ ball x (min (r/2) ((1/2 : ℝ)^m)),
      ∃ w ∈ activeLifts (Q n) a (P n) y, w ∉ U := by
    intro m
    have hd : 0 < min (r/2) ((1/2 : ℝ)^m) := lt_min (by positivity) (pow_pos (by norm_num) _)
    have hdr : min (r/2) ((1/2 : ℝ)^m) < r := (min_le_left _ _).trans_lt (by linarith)
    obtain ⟨n,hn,y,hy,hbad⟩ := hn _ hd hdr m
    obtain ⟨w,hw,hwu⟩ := Set.not_subset.mp hbad
    exact ⟨n,hn,y,hy,w,hw,hwu⟩
  choose k hk X hX W hW hbad using hex
  have hk' : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hXr : ∀ n, X n ∈ ball x r := fun n => (hX n).trans_le ((min_le_left _ _).trans (show r/2 ≤ r by linarith))
  have hXt : Tendsto X atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hX n).le.trans (min_le_right _ _))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨φ,_,w,hw,hwt⟩ := active_subseq_of_density_bound (locallyUniform_reindex hQ hk')
    (fun n => hconv (k n)) hq tendsto_const_nhds (fun n => hP (k n)) hp hx hXt
    (fun n => hball (hXr n)) hW (fun n => hD (k n) _ (hXr n) _ (hW n))
  obtain ⟨n,hn⟩ := (hwt.eventually (hU.mem_nhds (hAU hw))).exists
  exact hbad (φ n) hn

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LocalSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma supportOn_of_local {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x v : Parameter} (hx : x ∈ S)
    (hl : ∀ᶠ y in 𝓝 x, F x+pDot v (y-x) ≤ F y) : SupportOn S F x v := by
  intro y hy
  let Z : ℝ → Parameter := fun c => (1-c) • x+c • y
  have hcont : Continuous Z := by dsimp [Z]; fun_prop
  have hZ : Tendsto Z (𝓝 (0:ℝ)) (𝓝 x) := by simpa [Z] using hcont.tendsto 0
  obtain ⟨c,hc,hc1,hcl⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ F x+pDot v (Z c-x) ≤ F (Z c) := by
    have hmem : ∀ᶠ c in 𝓝[>] (0:ℝ), c ∈ Ioi 0 := self_mem_nhdsWithin
    have he : ∀ᶠ c in 𝓝[>] (0:ℝ),
        c ∈ Ioi 0 ∧ c < 1 ∧ F x+pDot v (Z c-x) ≤ F (Z c) :=
      hmem.and ((eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds |>.and
        ((hZ.eventually hl).filter_mono nhdsWithin_le_nhds))
    exact he.exists
  have hc0 : 0 ≤ 1-c := by linarith
  have hh := hF.2 hx hy hc0 hc.le (show (1-c)+c=1 by ring)
  have he : pDot v (Z c-x) = c*pDot v (y-x) := by dsimp [Z,pDot]; ring
  rw [he] at hcl
  change F (Z c) ≤ (1-c)*F x+c*F y at hh
  have hh' : c*(F x+pDot v (y-x)) ≤ c*F y := by nlinarith only [hcl,hh]
  exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm] using hh')

lemma supportOn_of_ball {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x v : Parameter} (hx : x ∈ S) {r : ℝ} (hr : 0 < r)
    (hl : SupportOn (ball x r) F x v) : SupportOn S F x v :=
  supportOn_of_local hF hx (mem_of_superset (ball_mem_nhds x hr) hl)

lemma support_of_interior_min {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x g : Parameter} (hx : x ∈ S) {T : Set Parameter}
    (hT : T ∈ 𝓝 x) (hmin : ∀ y ∈ T, F x-pDot g x ≤ F y-pDot g y) :
    SupportOn S F x g := by
  apply supportOn_of_local hF hx
  filter_upwards [hT] with y hy
  have hh := hmin y hy
  dsimp [pDot] at *
  linarith only [hh]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.NearbySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma support_ball_growth {F : Parameter → ℝ} {x g : Parameter} {γ : ℝ} (hγ : 0 ≤ γ)
    (hb : ∀ v ∈ closedBall g γ, SupportOn pressureDomain F x v)
    {y : Parameter} (hy : y ∈ pressureDomain) :
    γ*‖y-x‖ ≤ F y-F x-pDot g (y-x) := by
  have h1 := hb (g.1+γ,g.2) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  have h2 := hb (g.1-γ,g.2) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  have h3 := hb (g.1,g.2+γ) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  have h4 := hb (g.1,g.2-γ) (by simpa [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,abs_of_nonneg hγ] using hγ) y hy
  rw [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,Real.norm_eq_abs]
  dsimp [pDot] at *
  rcases le_total |y.1-x.1| |y.2-x.2| with hh | hh
  · rw [max_eq_right hh]
    rcases le_total 0 (y.2-x.2) with hs | hs
    · rw [abs_of_nonneg hs]; nlinarith only [h3]
    · rw [abs_of_nonpos hs]; nlinarith only [h4]
  · rw [max_eq_left hh]
    rcases le_total 0 (y.1-x.1) with hs | hs
    · rw [abs_of_nonneg hs]; nlinarith only [h1]
    · rw [abs_of_nonpos hs]; nlinarith only [h2]

lemma nearby_center_support {F Q P : Parameter → ℝ} {x g : Parameter} {γ r C S a : ℝ}
    (_hF : ConvexOn ℝ pressureDomain F) (hP : ConvexOn ℝ pressureDomain P)
    (_hx : x ∈ pressureDomain) (hγ : 0 < γ) (hS : 0 < S) (ha : 0 < a) (ha1 : a < 1)
    (hCS : C+2 < γ*S) (hr : S*a < r) (hball : ball x r ⊆ pressureDomain)
    (hsl : ∀ v ∈ closedBall g γ, SupportOn pressureDomain F x v)
    (happ : ∀ y ∈ ball x r, |Q y-F y| ≤ a^2)
    (hge : ∀ y ∈ ball x r, Q y ≤ P y) (hgain : P x ≤ Q x+C*a) :
    ∃ z ∈ ball x (S*a), SupportOn pressureDomain P z g := by
  have hSa : 0 < S*a := mul_pos hS ha
  have hr0 : 0 < r := hSa.trans hr
  have hsub : closedBall x (S*a) ⊆ ball x r := fun y hy => lt_of_le_of_lt hy hr
  have hcont : ContinuousOn (fun y => P y-pDot g y) (closedBall x (S*a)) :=
    (hP.continuousOn isOpen_pressureDomain |>.mono (hsub.trans hball)).sub
      (show Continuous (fun y => pDot g y) by unfold pDot; fun_prop).continuousOn
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall x (S*a)).exists_isMinOn
    ⟨x,mem_closedBall_self hSa.le⟩ hcont
  have hi : z ∈ ball x (S*a) := by
    by_contra hn
    have hd : dist z x = S*a := le_antisymm hz (le_of_not_gt hn)
    have hg := support_ball_growth hγ.le hsl (hball (hsub hz))
    have he1 := (abs_le.mp (happ z (hsub hz))).1
    have he2 := (abs_le.mp (happ x (mem_ball_self hr0))).2
    have he3 := hge z (hsub hz)
    have he4 := hmin (mem_closedBall_self hSa.le)
    change P z-pDot g z ≤ P x-pDot g x at he4
    rw [← dist_eq_norm_sub,hd] at hg
    have hex : pDot g (z-x) = pDot g z-pDot g x := by dsimp [pDot]; ring
    rw [hex] at hg
    have hmul := mul_lt_mul_of_pos_right hCS ha
    have hsq := mul_lt_mul_of_pos_left ha1 (show 0 < 2*a by positivity)
    nlinarith only [hg,he1,he2,he3,he4,hgain,hmul,hsq]
  refine ⟨z,hi,support_of_interior_min hP (hball (hsub hz)) ?_ (fun y hy => hmin hy)⟩
  exact mem_of_superset (isOpen_ball.mem_nhds hi) ball_subset_closedBall

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.UniformMin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma nearby_support_of_uniform {F P : Parameter → ℝ} (hP : ConvexOn ℝ pressureDomain P)
    {x g : Parameter} {γ r ε : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    (hball : closedBall x r ⊆ pressureDomain)
    (hsl : closedBall g γ ⊆ subgradients pressureDomain F x)
    (happ : ∀ y ∈ closedBall x r, |P y-F y| ≤ ε) (he : 2*ε < γ*r) :
    ∃ z ∈ ball x r, SupportOn pressureDomain P z g := by
  have hcont : ContinuousOn (fun y => P y-pDot g y) (closedBall x r) :=
    (hP.continuousOn isOpen_pressureDomain |>.mono hball).sub
      (show Continuous (fun y => pDot g y) by unfold pDot; fun_prop).continuousOn
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall x r).exists_isMinOn ⟨x,mem_closedBall_self hr.le⟩ hcont
  have hi : z ∈ ball x r := by
    by_contra hn
    have hd : dist z x = r := le_antisymm hz (le_of_not_gt hn)
    have hg := support_ball_growth hγ.le (fun v hv => hsl hv) (hball hz)
    have he1 := (abs_le.mp (happ z hz)).1
    have he2 := (abs_le.mp (happ x (mem_closedBall_self hr.le))).2
    have hm := hmin (mem_closedBall_self hr.le)
    change P z-pDot g z ≤ P x-pDot g x at hm
    rw [← dist_eq_norm_sub,hd] at hg
    have hex : pDot g (z-x)=pDot g z-pDot g x := by dsimp [pDot]; ring
    rw [hex] at hg
    linarith only [hg,he1,he2,hm,he]
  refine ⟨z,hi,support_of_interior_min hP (hball hz) ?_ (fun y hy => hmin hy)⟩
  exact mem_of_superset (isOpen_ball.mem_nhds hi) ball_subset_closedBall

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma initial_ball_moderate : closedBall initialPoint (1/2) ⊆ moderateBox := by
  intro x hx
  have hh : |x.1-1| ≤ 1/2 ∧ |x.2-(-3/4)| ≤ 1/2 := by
    simpa only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      Real.norm_eq_abs,max_le_iff,initialPoint] using hx
  obtain ⟨h1,h2⟩ := hh
  obtain ⟨h1,h1'⟩ := abs_le.mp h1
  obtain ⟨h2,h2'⟩ := abs_le.mp h2
  exact ⟨by linarith,by linarith,by linarith⟩

lemma moderateBox_subset : moderateBox ⊆ pressureDomain := by
  intro x hx
  change 0 < x.1
  linarith only [hx.1]

lemma physicalProfile_zero (t : ℝ) (R : ℕ → ℝ) :
    physicalProfile t (fun _ => 0) R = coreProfile t := by
  funext r
  simp [physicalProfile,attraction]

lemma physical_convex_bounded {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) :
    ConvexOn ℝ pressureDomain (physicalPressure (physicalProfile t σ R) t) := by
  have ht0 := lt_trans zero_lt_one ht
  exact convexOn_physicalPressure (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht
    (physicalProfile_stable ht0.le hσ hR hs (strengthened_smallness ht0 hm).1)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r)

lemma physical_meanField_bounded {t a : ℝ} (ht : 1 < t) (ha : 0 < a) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t) :
    IsMeanField (physicalPressure (physicalProfile t σ R) t) a
      (meanField (physicalPressure (physicalProfile t σ R) t) a) ∧
    (∀ x ∈ pressureDomain, ∃ d, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x) := by
  have ht0 := lt_trans zero_lt_one ht
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  exact ⟨isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le),
    fun _ hx => physical_meanField_attained ht ha hσ hR hs hsmall hgap hx⟩

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ApproximateSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma uniform_square_error_tendsto {F : Parameter → ℝ} {Q : ℕ → Parameter → ℝ}
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) {x : Parameter} {r : ℝ}
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Y : ℕ → Parameter} {y : Parameter} (hy : y ∈ ball x r)
    (hY : Tendsto Y atTop (𝓝 y)) (hF : ContinuousAt F y) :
    Tendsto (fun n => Q n (Y n)) atTop (𝓝 (F y)) := by
  have he : Tendsto (fun n => Q n (Y n)-F (Y n)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg (Q n (Y n)-F (Y n)))
      ((hY.eventually (isOpen_ball.mem_nhds hy)).mono fun n hn => happ n _ hn) (by simpa using ha.pow 2)
  have hh := he.add (hF.tendsto.comp hY)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hh

lemma approximate_support_limit {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {Q : ℕ → Parameter → ℝ} {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Y V : ℕ → Parameter} {v : Parameter}
    (hY : Tendsto Y atTop (𝓝 x)) (hV : Tendsto V atTop (𝓝 v))
    (hs : ∀ n, SupportOn pressureDomain (Q n) (Y n) (V n)) :
    SupportOn pressureDomain F x v := by
  apply supportOn_of_ball hF hx hr
  intro y hy
  have hcont := hF.continuousOn isOpen_pressureDomain
  have hqx := uniform_square_error_tendsto ha happ (mem_ball_self hr) hY
    (hcont.continuousAt (isOpen_pressureDomain.mem_nhds hx))
  have hqy := uniform_square_error_tendsto ha happ hy (tendsto_const_nhds (x := y))
    (hcont.continuousAt (isOpen_pressureDomain.mem_nhds (hball hy)))
  have hd : Tendsto (fun n => pDot (V n) (y-Y n)) atTop (𝓝 (pDot v (y-x))) := by
    exact (show Continuous (fun p : Parameter × Parameter => pDot p.1 (y-p.2)) by unfold pDot; fun_prop).tendsto
      (v,x) |>.comp (hV.prodMk_nhds hY)
  exact le_of_tendsto_of_tendsto (hqx.add hd) hqy (Eventually.of_forall fun n => hs n y (hball hy))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ScaledActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma scaled_active_limit {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {Q P : ℕ → Parameter → ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    {x ξ v : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Ξ W : ℕ → Parameter} (hΞ : Tendsto Ξ atTop (𝓝 ξ)) (hW : Tendsto W atTop (𝓝 v))
    (hXS : ∀ n, x+a n • Ξ n ∈ pressureDomain)
    (hA : ∀ n, W n ∈ activeLifts (Q n) (a n) (P n) (x+a n • Ξ n)) :
    SupportOn pressureDomain F x v ∧
      ∀ u, SupportOn pressureDomain F x u → quadraticObjective ξ u x.1 ≤ quadraticObjective ξ v x.1 := by
  let X : ℕ → Parameter := fun n => x+a n • Ξ n
  let V : ℕ → Parameter := fun n => unlift (a n) (W n)
  let Y : ℕ → Parameter := fun n => shiftedField (a n) (X n) (W n).2
  have hX : Tendsto X atTop (𝓝 x) := by
    simpa only [zero_smul,add_zero] using tendsto_const_nhds.add (ha0.smul hΞ)
  have hw2 := (continuous_snd.tendsto v).comp hW
  have hV : Tendsto V atTop (𝓝 v) := by
    have hh := (((continuous_fst.tendsto v).comp hW).sub ((ha0.mul (hw2.pow 2)).div_const 2)).prodMk_nhds hw2
    simpa only [Function.comp_def,V,unlift,zero_mul,zero_div,sub_zero,Prod.mk.eta] using hh
  have hY : Tendsto Y atTop (𝓝 x) := by
    have hh := ((continuous_fst.tendsto x).comp hX).prodMk_nhds
      (((continuous_snd.tendsto x).comp hX).add
        ((((continuous_fst.tendsto x).comp hX).mul ha0).mul hw2))
    simpa only [Function.comp_def,Y,shiftedField,mul_zero,zero_mul,add_zero,Prod.mk.eta] using hh
  have hv := approximate_support_limit hF ha0 hx hr hball happ hY hV (fun n => (hA n).2)
  refine ⟨hv,?_⟩
  intro u hu
  let Z : ℕ → Parameter := fun n => shiftedField (a n) (X n) u.2
  have hZ : Tendsto Z atTop (𝓝 x) := by
    have hh := ((continuous_fst.tendsto x).comp hX).prodMk_nhds
      (((continuous_snd.tendsto x).comp hX).add
        ((((continuous_fst.tendsto x).comp hX).mul ha0).mul_const u.2))
    simpa only [Function.comp_def,Z,shiftedField,mul_zero,zero_mul,add_zero,Prod.mk.eta] using hh
  have hineq : ∀ᶠ n in atTop,
      pDot u (Ξ n)+(X n).1*u.2^2/2 ≤ pDot (V n) (Ξ n)+(X n).1*(W n).2^2/2+2*a n := by
    filter_upwards [hZ.eventually (ball_mem_nhds x hr)] with n hn
    have h1 := hu (Z n) (hball hn)
    have h2 := (hA n).2 x hx
    have h3 := (hP n (X n) (hXS n)).1 (mem_range_self u.2)
    have h4 := (hA n).1
    have h5 := (abs_le.mp (happ n (Z n) hn)).1
    have h6 := (abs_le.mp (happ n x (mem_ball_self hr))).2
    have he1 : pDot u (Z n-x) = a n*(pDot u (Ξ n)+(X n).1*u.2^2) := by dsimp [Z,shiftedField,X,pDot]; ring
    have he2 : pDot (unlift (a n) (W n)) (x-Y n) =
        -(a n*(pDot (V n) (Ξ n)+(X n).1*(W n).2^2)) := by dsimp [Y,X,shiftedField,V,unlift,pDot]; ring
    rw [he1] at h1
    change Q n (Y n)+pDot (unlift (a n) (W n)) (x-Y n) ≤ Q n x at h2
    rw [he2] at h2
    change Q n (Z n)-(X n).1*a n*u.2^2/2 ≤ P n (X n) at h3
    change Q n (Y n)-(X n).1*a n*(W n).2^2/2 = P n (X n) at h4
    have hmul : a n*(pDot u (Ξ n)+(X n).1*u.2^2/2) ≤
        a n*(pDot (V n) (Ξ n)+(X n).1*(W n).2^2/2+2*a n) := by
      nlinarith only [h1,h2,h3,h4,h5,h6]
    exact (mul_le_mul_iff_right₀ (ha n)).mp (by simpa only [mul_comm] using hmul)
  have hdotu : Tendsto (fun n => pDot u (Ξ n)) atTop (𝓝 (pDot u ξ)) :=
    (show Continuous (fun z => pDot u z) by unfold pDot; fun_prop).tendsto ξ |>.comp hΞ
  have hdotv : Tendsto (fun n => pDot (V n) (Ξ n)) atTop (𝓝 (pDot v ξ)) :=
    (show Continuous (fun p : Parameter × Parameter => pDot p.1 p.2) by unfold pDot; fun_prop).tendsto
      (v,ξ) |>.comp (hV.prodMk_nhds hΞ)
  have ht1 := (continuous_fst.tendsto x).comp hX
  have hh := le_of_tendsto_of_tendsto (hdotu.add ((ht1.mul_const (u.2^2)).div_const 2))
    ((hdotv.add ((ht1.mul (hw2.pow 2)).div_const 2)).add (ha0.const_mul 2)) hineq
  dsimp only [quadraticObjective,pDot]
  dsimp only [pDot] at hh
  nlinarith only [hh]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ScaledBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma bounded_zero_mul {a d : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {D : ℝ} (hd : ∀ n, |d n| ≤ D) : Tendsto (fun n => a n*d n) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hh : Tendsto (fun n => |a n| * D) atTop (𝓝 0) := by simpa using (ha.abs.mul_const D)
  apply squeeze_zero (fun n => abs_nonneg _) _ hh
  intro n
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hd n) (abs_nonneg _)

lemma scaled_active_subseq {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {Q P : ℕ → Parameter → ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hQ : ∀ n, ConvexOn ℝ pressureDomain (Q n)) (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Ξ W : ℕ → Parameter} {S D : ℝ} (hΞ : ∀ n, ‖Ξ n‖ ≤ S)
    (hXS : ∀ n, x+a n • Ξ n ∈ pressureDomain)
    (hA : ∀ n, W n ∈ activeLifts (Q n) (a n) (P n) (x+a n • Ξ n))
    (hD : ∀ n, |(W n).2| ≤ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ξ v : Parameter,
      Tendsto (Ξ ∘ φ) atTop (𝓝 ξ) ∧ Tendsto (W ∘ φ) atTop (𝓝 v) ∧
      SupportOn pressureDomain F x v ∧
      ∀ u, SupportOn pressureDomain F x u → quadraticObjective ξ u x.1 ≤ quadraticObjective ξ v x.1 := by
  obtain ⟨ξ,_,φ,hφ,hξ⟩ := (isCompact_closedBall (0 : Parameter) S).tendsto_subseq
    (fun n => by simpa only [mem_closedBall,dist_zero_right] using hΞ n)
  let b := a ∘ φ
  let X : ℕ → Parameter := fun n => x+b n • Ξ (φ n)
  let Y : ℕ → Parameter := fun n => shiftedField (b n) (X n) (W (φ n)).2
  let V : ℕ → Parameter := fun n => unlift (b n) (W (φ n))
  have hb : Tendsto b atTop (𝓝 0) := ha0.comp hφ.tendsto_atTop
  have hX : Tendsto X atTop (𝓝 x) := by
    simpa only [Function.comp_def,X,zero_smul,add_zero] using tendsto_const_nhds.add (hb.smul hξ)
  have hY : Tendsto Y atTop (𝓝 x) := by
    have hh := ((continuous_fst.tendsto x).comp hX).prodMk_nhds
      (((continuous_snd.tendsto x).comp hX).add
        (((continuous_fst.tendsto x).comp hX).mul (bounded_zero_mul hb (fun n => hD (φ n)))))
    simpa only [Function.comp_def,Y,shiftedField,mul_zero,add_zero,Prod.mk.eta,mul_assoc] using hh
  have hpoint : ∀ y ∈ ball x r, Tendsto (fun n => Q (φ n) y) atTop (𝓝 (F y)) := by
    intro y hy
    exact uniform_square_error_tendsto hb (fun n => happ (φ n)) hy tendsto_const_nhds
      ((hF.continuousOn isOpen_pressureDomain).continuousAt (isOpen_pressureDomain.mem_nhds (hball hy)))
  obtain ⟨C,hC⟩ := eventually_subgradients_bounded isOpen_ball
    (Eventually.of_forall fun n => (hQ (φ n)).subset hball (convex_ball x r)) hpoint
    (mem_ball_self hr) hY
  have hVC : ∀ᶠ n in atTop, V n ∈ closedBall 0 C := by
    filter_upwards [hC] with n hn
    simpa only [mem_closedBall,dist_zero_right] using hn (V n) (fun y hy => (hA (φ n)).2 y (hball hy))
  obtain ⟨v,_,ψ,hψ,hv⟩ := (isCompact_closedBall (0 : Parameter) C).tendsto_subseq' hVC.frequently
  have hw : Tendsto (W ∘ (φ ∘ ψ)) atTop (𝓝 v) := by
    have hd2 : ∀ n, |(W (φ (ψ n))).2^2| ≤ D^2 := by
      intro n
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hD (φ (ψ n))) 2
    have he := (bounded_zero_mul (hb.comp hψ.tendsto_atTop) hd2).div_const 2
    have hh := (((continuous_fst.tendsto v).comp hv).add he).prodMk_nhds
      ((continuous_snd.tendsto v).comp hv)
    simpa only [Function.comp_def,V,unlift,b,zero_div,add_zero,sub_add_cancel,Prod.mk.eta] using hh
  have hxi := hξ.comp hψ.tendsto_atTop
  have hb0 := ha0.comp (hφ.comp hψ).tendsto_atTop
  have hh := scaled_active_limit hF (fun n => ha (φ (ψ n))) hb0
    (fun n => hP (φ (ψ n))) hx hr hball (fun n => happ (φ (ψ n))) hxi hw
    (fun n => hXS (φ (ψ n))) (fun n => hA (φ (ψ n)))
  exact ⟨φ ∘ ψ,hφ.comp hψ,ξ,v,hxi,hw,hh⟩

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ScaledLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma scaled_localization {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    {κ : Type u_1} (K : κ → Set Parameter) (hc : ∀ i, Convex ℝ (K i))
    (hsep : ∀ i j, i ≠ j → Disjoint (Prod.snd '' K i) (Prod.snd '' K j))
    (hK : subgradients pressureDomain F x = convexHull ℝ (⋃ i, K i))
    {U : Set Parameter} (hU : IsOpen U) (hKU : (⋃ i, K i) ⊆ U) (S D : ℝ) :
    ∃ δ > 0, ∀ a : ℝ, 0 < a → a < δ → ∀ Q P : Parameter → ℝ,
      ConvexOn ℝ pressureDomain Q → IsMeanField Q a P →
      (∀ y ∈ ball x r, |Q y-F y| ≤ a^2) →
      ∀ Ξ : Parameter, ‖Ξ‖ ≤ S → x+a • Ξ ∈ pressureDomain →
      ∀ w ∈ activeLifts Q a P (x+a • Ξ), |w.2| ≤ D → w ∈ U := by
  by_contra hn
  push Not at hn
  have hex : ∀ n : ℕ, ∃ a : ℝ, 0 < a ∧ a < (1/2 : ℝ)^n ∧
      ∃ Q P : Parameter → ℝ, ConvexOn ℝ pressureDomain Q ∧ IsMeanField Q a P ∧
      (∀ y ∈ ball x r, |Q y-F y| ≤ a^2) ∧ ∃ Ξ : Parameter, ‖Ξ‖ ≤ S ∧
      x+a • Ξ ∈ pressureDomain ∧ ∃ w ∈ activeLifts Q a P (x+a • Ξ), |w.2| ≤ D ∧ w ∉ U :=
    fun n => hn _ (pow_pos (by norm_num) n)
  choose a ha ha' Q P hQ hP happ Ξ hΞ hXS W hW hD hbad using hex
  have ha0 : Tendsto a atTop (𝓝 0) :=
    squeeze_zero (fun n => (ha n).le) (fun n => (ha' n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨φ,_,ξ,v,_,hv,hs,hm⟩ := scaled_active_subseq hF ha ha0 hQ hP hx hr hball happ hΞ hXS hW hD
  have hvs : v ∈ convexHull ℝ (⋃ i, K i) := by rw [← hK]; exact hs
  have hu := hKU (quadratic_maximizer_mem_group K hc hsep hx hvs (fun u hu => hm u (by change u ∈ subgradients pressureDomain F x; rw [hK]; exact hu)))
  obtain ⟨n,hn⟩ := (hv.eventually (hU.mem_nhds hu)).exists
  exact hbad (φ n) hn

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Persistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma three_group_persistence {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {x g : Parameter} (hx : x ∈ pressureDomain) {r γ : ℝ} (hr : 0 < r) (hγ : 0 < γ)
    (hball : ball x r ⊆ pressureDomain)
    (hsl : closedBall g γ ⊆ subgradients pressureDomain F x)
    {K : Fin 3 → Set Parameter} (hc : ∀ i, Convex ℝ (K i))
    (hsep : ∀ i j, i ≠ j → Disjoint (Prod.snd '' K i) (Prod.snd '' K j))
    (hK : subgradients pressureDomain F x = convexHull ℝ (⋃ i, K i))
    {v : Fin 3 → Parameter} {b ε : ℝ} (hε : 0 < ε)
    (hKv : ∀ i, K i ⊆ closedBall (v i) b) (C D : ℝ) :
    ∃ S > 0, ∃ δ > 0, ∀ a : ℝ, 0 < a → a < δ → ∀ Q P : Parameter → ℝ,
      ConvexOn ℝ pressureDomain Q → IsMeanField Q a P →
      (∀ y ∈ pressureDomain, ∃ d, quadraticCost Q a y d=P y) →
      (∀ y ∈ ball x r, |Q y-F y| ≤ a^2) → P x ≤ Q x+C*a →
      (∀ y ∈ ball x r, ∀ w ∈ activeLifts Q a P y, |w.2| ≤ D) →
      ∃ z ∈ ball x (S*a), z ∈ ball x r ∧ SupportOn pressureDomain P z g ∧
        subgradients pressureDomain P z = convexHull ℝ (⋃ i, slopeGroups P z v (b+ε) i) := by
  let S : ℝ := (|C|+3)/γ
  have hS : 0 < S := div_pos (by positivity) hγ
  have hCS : C+2 < γ*S := by
    have he : γ*S=|C|+3 := by dsimp [S]; field_simp
    rw [he]
    linarith only [le_abs_self C]
  let U := ⋃ i, ball (v i) (b+ε)
  have hU : IsOpen U := isOpen_iUnion (fun i => isOpen_ball)
  have hKU : (⋃ i, K i) ⊆ U := by
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp hw
    exact mem_iUnion.mpr ⟨i,lt_of_le_of_lt (hKv i hi) (show b < b+ε by linarith)⟩
  obtain ⟨δ,hδ,hloc⟩ := scaled_localization hF hx hr hball K hc hsep hK hU hKU S D
  refine ⟨S,hS,min 1 (min (r/S) δ),lt_min zero_lt_one (lt_min (div_pos hr hS) hδ),?_⟩
  intro a ha had Q P hQ hP hatt happ hgain hD
  have ha1 := had.trans_le (min_le_left _ _)
  have haδ := had.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have har := had.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hSa : S*a < r := by nlinarith only [(lt_div_iff₀ hS).mp har]
  obtain ⟨z,hz,hg⟩ := nearby_center_support hF (meanField_convex hQ hP) hx hγ hS ha ha1 hCS hSa hball
    (fun w hw => hsl hw) happ (fun y hy => meanField_ge_base hP (hball hy)) hgain
  have hzr : z ∈ ball x r := hz.trans hSa
  let Ξ := a⁻¹ • (z-x)
  have hrep : x+a • Ξ=z := by
    dsimp [Ξ]
    rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul,add_sub_cancel]
  have hΞ : ‖Ξ‖ ≤ S := by
    dsimp [Ξ]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),← div_eq_inv_mul]
    apply (div_le_iff₀ ha).mpr
    have hzl : dist z x ≤ S*a := le_of_lt hz
    simpa only [← dist_eq_norm_sub] using hzl
  refine ⟨z,hz,hzr,hg,regroup_active ha hQ hP hatt (hball hzr) ?_⟩
  intro w hw
  have he := hloc a ha haδ Q P hQ hP happ Ξ hΞ (hrep.symm ▸ hball hzr) w (hrep.symm ▸ hw)
    (hD z hzr w hw)
  change w ∈ ⋃ i, ball (v i) (b+ε) at he
  obtain ⟨i,hi⟩ := mem_iUnion.mp he
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  change dist w (v i) ≤ b+ε
  exact le_of_lt hi

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TripleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma HasVertexTriple.support_ball {P : Parameter → ℝ} {x : Parameter} {p b τ γ : ℝ}
    (h : HasVertexTriple P x p b) (hp : 0 < p) (hb : b ≤ τ) (hτ : τ ≤ p/100)
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w)) :
    closedBall (triangleCenter p) γ ⊆ subgradients pressureDomain P x := by
  have hK (i : Fin 3) : slopeGroups P x (triangleVertex p) b i ⊆ closedBall (triangleVertex p i) τ :=
    inter_subset_right.trans (closedBall_subset_closedBall hb)
  exact support_ball_of_vertex_groups hgeom
    (all_vertex_groups_nonempty hp hτ _ hK (h.hull ▸ h.center)) hK h.hull

lemma HasVertexTriple.separated {P : Parameter → ℝ} {x : Parameter} {p b : ℝ}
    (hp : 0 < p) (hb : b ≤ p/100) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (Prod.snd '' slopeGroups P x (triangleVertex p) b i)
      (Prod.snd '' slopeGroups P x (triangleVertex p) b j) :=
  (vertex_density_separation hp hb hij).mono (image_mono inter_subset_right) (image_mono inter_subset_right)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma ConstructionCap.weak {t M m : ℝ} (h : ConstructionCap t M) (hm : m ≤ M) :
    17576*kernelHeight*m ≤ t := by
  calc
    17576*kernelHeight*m ≤ 17576*kernelHeight*M := mul_le_mul_of_nonneg_left hm (by positivity [kernelHeight_pos])
    _ ≤ 140608*kernelHeight*M := by nlinarith only [mul_pos kernelHeight_pos h.mass_pos]
    _ ≤ t := h.strong

lemma ConstructionCap.lt_gap {t M a : ℝ} (h : ConstructionCap t M) (ha : a ≤ M) :
    1024*a < t := (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_lt h.gap

lemma exists_constructionCap {M : ℝ} (hM : 0 < M) : ∃ T : ℝ, ConstructionCap T M := by
  obtain ⟨T,hT⟩ := exists_gt (max 1 (max (140608*kernelHeight*M) (1024*M)))
  refine ⟨T,?_,hM,?_,?_⟩
  · exact (le_max_left _ _).trans_lt hT
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hT.le
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT

lemma ConstructionCap.mono_t {t T M : ℝ} (h : ConstructionCap T M) (ht : T ≤ t) :
    ConstructionCap t M := ⟨h.t_large.trans_le ht,h.mass_pos,h.strong.trans ht,h.gap.trans_le ht⟩

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.InitialTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma initial_triple_of_limits {p τ γ r : ℝ} (hp : 0 < p) (hτ : 0 < τ)
    (hγ : 0 < γ) (hr : 0 < r) (hr' : r < 1/2)
    (hgeom : closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range (triangleVertex p)))
    {Q P : ℕ → Parameter → ℝ}
    (hQ : TendstoLocallyUniformlyOn Q (threeCore p) atTop pressureDomain)
    (hQc : ∀ n, ConvexOn ℝ pressureDomain (Q n))
    (hP : ∀ n, IsMeanField (Q n) (firstMass p) (P n))
    (hatt : ∀ n, ∀ y ∈ pressureDomain, ∃ d, quadraticCost (Q n) (firstMass p) y d = P n y)
    (hPt : TendstoLocallyUniformlyOn P (threeMeanField p (firstMass p)) atTop (ball initialPoint (1/2)))
    (hD : ∀ n, ∀ y ∈ ball initialPoint (1/2), ∀ w ∈ activeLifts (Q n) (firstMass p) (P n) y,
      w.2 ∈ Icc (0:ℝ) 1048576) (N : ℕ) :
    ∃ n ≥ N, ∃ x ∈ ball initialPoint r, HasVertexTriple (P n) x p (τ/2) := by
  let U := ⋃ i : Fin 3, ball (triangleVertex p i) (τ/2)
  have hAU : activeLifts (threeCore p) (firstMass p) (threeMeanField p (firstMass p)) initialPoint ⊆ U := by
    intro w hw
    obtain ⟨i,rfl⟩ := three_active_initial hp hw
    exact mem_iUnion.mpr ⟨i,mem_ball_self (by positivity)⟩
  have hball : ball initialPoint (1/2) ⊆ pressureDomain :=
    ball_subset_closedBall.trans (initial_ball_moderate.trans moderateBox_subset)
  obtain ⟨δ,hδ,hδ',M,hM⟩ := active_uniform_near hQ hQc
    ((threeCore_convex p).continuousOn isOpen_pressureDomain) hP (three_meanField (firstMass_pos hp).le)
    (show initialPoint ∈ pressureDomain by norm_num [initialPoint,pressureDomain])
    (show (0:ℝ) < 1/2 by norm_num) hball hD (isOpen_iUnion fun _ => isOpen_ball) hAU
  let s := min r (δ/2)
  have hs : 0 < s := lt_min hr (by positivity)
  have hsr : s ≤ r := min_le_left _ _
  have hsd : s < δ := (min_le_right _ _).trans_lt (by linarith)
  have hsW : closedBall initialPoint s ⊆ ball initialPoint (1/2) :=
    fun _ hx => hx.trans_lt (hsr.trans_lt hr')
  have huni := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall initialPoint s)).mp (hPt.mono hsW)
  have he : 0 < γ*s/4 := by positivity
  have happ := (Metric.tendstoUniformlyOn_iff.mp huni) (γ*s/4) he
  obtain ⟨n,hn,hN,hMn⟩ := (happ.and ((eventually_ge_atTop N).and (eventually_ge_atTop M))).exists
  have hc := meanField_convex (hQc n) (hP n)
  obtain ⟨x,hx,hgx⟩ := nearby_support_of_uniform hc hγ hs (hsW.trans hball)
    (hgeom.trans (three_support_contains_triangle hp))
    (fun y hy => by have hh := hn y hy; simpa only [Real.dist_eq,abs_sub_comm] using hh.le)
    (show 2*(γ*s/4) < γ*s by nlinarith only [mul_pos hγ hs])
  refine ⟨n,hN,x,hx.trans_le hsr,hgx,regroup_active (firstMass_pos hp) (hQc n) (hP n) (hatt n)
    (hball (hx.trans (hsr.trans_lt hr'))) ?_⟩
  intro w hw
  have hh := hM n hMn x (hx.trans hsd) hw
  obtain ⟨i,hi⟩ := mem_iUnion.mp hh
  exact mem_iUnion.mpr ⟨i,show dist w (triangleVertex p i) ≤ τ/2 from le_of_lt hi⟩

lemma physical_initial_triple {τ γ r T : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    (hr : 0 < r) (hr' : r < 1/2) (hT : 1 < T) (hTa : 1024*firstMass packingDensity < T)
    (hgeom : closedBall (triangleCenter packingDensity) γ ⊆ convexHull ℝ (range (triangleVertex packingDensity))) :
    ∃ t ≥ T, ∃ x ∈ ball initialPoint r,
      HasVertexTriple (meanField (physicalPressure (coreProfile t) t) (firstMass packingDensity)) x packingDensity (τ/2) := by
  let a := firstMass packingDensity
  have ha : 0 < a := firstMass_pos packingDensity_pos
  let Q := fun n : ℕ => physicalPressure (coreProfile ((n:ℝ)+T)) ((n:ℝ)+T)
  have ht (n : ℕ) : 1 < (n:ℝ)+T := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hat (n : ℕ) : 1024*a < (n:ℝ)+T := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm (n : ℕ) : 17576*kernelHeight*(∑' _ : ℕ, (0:ℝ)) ≤ (n:ℝ)+T := by simp; linarith [ht n]
  have hQc (n : ℕ) : ConvexOn ℝ pressureDomain (Q n) := by
    simpa only [physicalProfile_zero] using physical_convex_bounded (ht n)
      (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (hm n)
  have hPQ (n : ℕ) := physical_meanField_bounded (ht n) ha
    (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (hm n) (hat n)
  simp only [physicalProfile_zero] at hPQ
  obtain ⟨n,_,x,hx,htr⟩ := initial_triple_of_limits packingDensity_pos hτ hγ hr hr' hgeom
    (locallyUniform_reindex core_pressure_locally_uniform (tendsto_atTop_add_const_right atTop T tendsto_natCast_atTop_atTop))
    hQc (fun n => (hPQ n).1) (fun n => (hPQ n).2) (core_transform_locally_uniform hT ha hTa)
    (fun n y hy w hw => by
      have hh := initial_ball_moderate (ball_subset_closedBall hy)
      exact physical_transform_active_bound (ht n) ha
        (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (hm n) (hat n)
        hh.1 hh.2.1 hh.2.2 (by simpa only [physicalProfile_zero] using hw)) 0
  exact ⟨(n:ℝ)+T,by linarith [Nat.cast_nonneg (α := ℝ) n],x,hx,htr⟩

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma geometricBudget_pos (n : ℕ) : 0 < geometricBudget n := pow_pos (by norm_num) _
lemma geometricBudget_succ (n : ℕ) : geometricBudget (n+1) = geometricBudget n/2 := by
  unfold geometricBudget
  rw [pow_succ]
  ring
lemma groupRadius_le {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) : groupRadius τ n ≤ τ := by
  dsimp [groupRadius]
  nlinarith only [mul_nonneg hτ (geometricBudget_pos (n+1)).le]
lemma groupRadius_succ (τ : ℝ) (n : ℕ) :
    groupRadius τ (n+1) = groupRadius τ n+τ*geometricBudget n/4 := by
  simp only [groupRadius,geometricBudget_succ]
  ring
lemma locationRadius_lt (n : ℕ) : locationRadius n < 1/8 := by
  dsimp [locationRadius]
  linarith only [geometricBudget_pos n]
lemma locationRadius_succ (n : ℕ) : locationRadius (n+1)=locationRadius n+geometricBudget n/32 := by
  simp only [locationRadius,geometricBudget_succ]
  ring

lemma ConstructionStage.mass_total {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.a+∑' k, s.σ k ≤ firstMass p+1 :=
  s.mass.trans (sub_le_self _ (geometricBudget_pos n).le)

lemma ConstructionStage.base_mass {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    ∑' k, s.σ k ≤ firstMass p+1 := by
  linarith only [s.mass_total,s.a_pos]

lemma ConstructionStage.a_le {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.a ≤ firstMass p+1 := by
  have hh : 0 ≤ ∑' k, s.σ k := tsum_nonneg s.σ_nonneg
  linarith only [s.mass_total,hh]

lemma ConstructionStage.x_near {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.x ∈ ball initialPoint (1/8) := s.location.trans (locationRadius_lt n)

lemma ConstructionStage.near_moderate {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    ball s.x (1/8) ⊆ closedBall initialPoint (1/4) := by
  intro y hy
  exact le_of_lt (calc
    dist y initialPoint ≤ dist y s.x+dist s.x initialPoint := dist_triangle _ _ _
    _ < 1/4 := by have hh := s.x_near; change dist s.x initialPoint < 1/8 at hh; change dist y s.x < 1/8 at hy; linarith)

lemma ConstructionStage.convex {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n)
    (hcap : ConstructionCap t (firstMass p+1)) : ConvexOn ℝ pressureDomain s.ideal := by
  exact meanField_convex (physical_convex_bounded hcap.t_large s.σ_nonneg s.R_one s.σ_summable (hcap.weak s.base_mass))
    (physical_meanField_bounded hcap.t_large s.a_pos s.σ_nonneg s.R_one s.σ_summable
      (hcap.weak s.base_mass) (hcap.lt_gap s.a_le)).1

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma construction_step {t p τ γ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hτp : τ ≤ p/100)
    (hγ : 0 < γ) (hcap : ConstructionCap t (firstMass p+1))
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    {n : ℕ} (s : ConstructionStage t p τ n) :
    ∃ s' : ConstructionStage t p τ (n+1), ∃ Rnew, StageTransition s s' Rnew := by
  have hWmod : closedBall initialPoint (1/4) ⊆ moderateBox :=
    (closedBall_subset_closedBall (by norm_num : (1:ℝ)/4 ≤ 1/2)).trans initial_ball_moderate
  have hball := s.near_moderate.trans (hWmod.trans moderateBox_subset)
  have hxmod : s.x ∈ moderateBox := hWmod (s.x_near.le.trans (by norm_num : (1:ℝ)/8 ≤ 1/4))
  have hxdom := moderateBox_subset hxmod
  have hsl := s.triple.support_ball hp (groupRadius_le hτ.le n) hτp hgeom
  have hb : groupRadius τ n ≤ p/100 := (groupRadius_le hτ.le n).trans hτp
  let ε := τ*geometricBudget n/4
  have hε : 0 < ε := by dsimp [ε]; positivity [geometricBudget_pos n]
  obtain ⟨S,hS,δ,hδ,hpersist⟩ := three_group_persistence (s.convex hcap) hxdom
    (show (0:ℝ) < 1/8 by norm_num) hγ hball hsl
    (slopeGroups_convex s.ideal s.x (triangleVertex p) (groupRadius τ n))
    (fun i j hij => HasVertexTriple.separated hp hb i j hij) s.triple.hull hε
    (fun _ => inter_subset_right) (1048576^2) 1048576
  let ell := geometricBudget n/32
  have hell : 0 < ell := by dsimp [ell]; positivity [geometricBudget_pos n]
  let a := min δ (min (ell/(S+1)) (geometricBudget n/2))/2
  have ha : 0 < a := by dsimp [a]; positivity [geometricBudget_pos n]
  have ham : a < min δ (min (ell/(S+1)) (geometricBudget n/2)) := by dsimp [a] at ha ⊢; linarith
  have haδ : a < δ := ham.trans_le (min_le_left _ _)
  have haell : a < ell/(S+1) := ham.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hapow : a < geometricBudget n/2 := ham.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hSa : S*a < ell := by
    have hh := (lt_div_iff₀ (show 0 < S+1 by linarith)).mp haell
    nlinarith only [hh,ha]
  obtain ⟨B,hB,hbound⟩ := s.referenceBounded
  have hprec : 0 < min (a^2) (geometricBudget n) := lt_min (sq_pos_of_pos ha) (geometricBudget_pos n)
  obtain ⟨Rnew,hRnew,hRbig,happ⟩ := physical_kac_approximate hcap s.a_pos s.σ_nonneg s.R_one s.σ_summable
    s.mass_total hB hbound hprec (B+1)
  let σ' := prepend s.a s.σ
  let R' := prepend Rnew s.R
  have hσ' : ∀ k, 0 ≤ σ' k := prepend_nonneg s.a_pos.le s.σ_nonneg
  have hR' : ∀ k, 1 ≤ R' k := prepend_ge_one (by linarith) s.R_one
  have hs' : Summable σ' := summable_prepend s.a s.σ_summable
  have hmass' : ∑' k, σ' k = s.a+∑' k, s.σ k := tsum_prepend s.a s.σ_summable
  have hm' : ∑' k, σ' k ≤ firstMass p+1 := hmass' ▸ s.mass_total
  have htot : a+∑' k, σ' k ≤ firstMass p+1-geometricBudget (n+1) := by
    rw [hmass',geometricBudget_succ]
    linarith only [s.mass,hapow]
  have haM : a ≤ firstMass p+1 := by
    have hh : 0 ≤ ∑' k, σ' k := tsum_nonneg hσ'
    have hh' := geometricBudget_pos (n+1)
    linarith only [htot,hh,hh']
  let Q := physicalPressure (physicalProfile t σ' R') t
  let P := meanField Q a
  have hQ := physical_convex_bounded hcap.t_large hσ' hR' hs' (hcap.weak hm')
  have hMF := physical_meanField_bounded hcap.t_large ha hσ' hR' hs' (hcap.weak hm') (hcap.lt_gap haM)
  obtain ⟨z,hz,hzr,hg,hull⟩ := hpersist a ha haδ Q P hQ hMF.1 hMF.2
    (fun y hy => (happ y (s.near_moderate hy)).trans (min_le_left _ _))
    (physical_transform_gain hcap.t_large ha hσ' hR' hs' (hcap.weak hm') (hcap.lt_gap haM)
      hxmod.1 hxmod.2.1 hxmod.2.2)
    (fun y hy w hw => by
      have hh := hWmod (s.near_moderate hy)
      have hd := physical_transform_active_bound hcap.t_large ha hσ' hR' hs' (hcap.weak hm') (hcap.lt_gap haM)
        hh.1 hh.2.1 hh.2.2 hw
      simpa only [abs_of_nonneg hd.1] using hd.2)
  have hdisp : dist z s.x < geometricBudget n/32 := hz.trans hSa
  let s' : ConstructionStage t p τ (n+1) := {
    σ := σ', R := R', a := a, x := z,
    σ_nonneg := hσ', R_one := hR', σ_summable := hs', a_pos := ha, mass := htot,
    referenceBounded := ⟨Rnew,by linarith,by
      intro k hk
      cases k with
      | zero => exact le_refl _
      | succ k => exact (hbound k hk).trans (by linarith)⟩,
    location := by
      rw [locationRadius_succ]
      have hh := dist_triangle z s.x initialPoint
      linarith only [hh,hdisp,s.location],
    triple := ⟨hg,by rw [groupRadius_succ]; exact hull⟩ }
  refine ⟨s',Rnew,hRnew,rfl,rfl,hapow,hdisp,?_⟩
  intro y hy
  exact (happ y hy).trans (min_le_right _ _)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma sequence_of_initial {t p τ γ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hτp : τ ≤ p/100)
    (hγ : 0 < γ) (hcap : ConstructionCap t (firstMass p+1))
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    (s₀ : ConstructionStage t p τ 0) (hzero : s₀.σ = fun _ => 0) (hfirst : s₀.a = firstMass p) :
    Nonempty (ConstructionData p) := by
  have hex := fun n (s : ConstructionStage t p τ n) => construction_step hp hτ hτp hγ hcap hgeom s
  let next := fun n (s : ConstructionStage t p τ n) => Classical.choose (hex n s)
  let length := fun n (s : ConstructionStage t p τ n) => Classical.choose (Classical.choose_spec (hex n s))
  have hn (n) (s : ConstructionStage t p τ n) : StageTransition s (next n s) (length n s) :=
    Classical.choose_spec (Classical.choose_spec (hex n s))
  let seq : ∀ n, ConstructionStage t p τ n := Nat.rec s₀ (fun n s => next n s)
  refine ⟨⟨t,τ,γ,hτ,hτp,hγ,hcap,hgeom,seq,(fun n => length n (seq n)),hzero,hfirst,?_⟩⟩
  intro n
  exact hn n (seq n)

lemma exists_constructionData_oai : Nonempty (ConstructionData packingDensity) := by
  have hp := packingDensity_pos
  obtain ⟨τ₀,γ,hτ₀,hγ,hgeom₀⟩ := robust_vertex_triangle hp
  let τ := min τ₀ (packingDensity/100)
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hτp : τ ≤ packingDensity/100 := min_le_right _ _
  have hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex packingDensity i) ≤ τ) →
      closedBall (triangleCenter packingDensity) γ ⊆ convexHull ℝ (range w) :=
    fun w hw => hgeom₀ w (fun i => (hw i).trans (min_le_left _ _))
  have ha : 0 < firstMass packingDensity := firstMass_pos hp
  obtain ⟨T,hT⟩ := exists_constructionCap (show 0 < firstMass packingDensity+1 by linarith)
  obtain ⟨t,ht,x,hx,htr⟩ := physical_initial_triple hτ hγ (show (0:ℝ) < 1/64 by norm_num)
    (show (1:ℝ)/64 < 1/2 by norm_num) hT.t_large (hT.lt_gap (by linarith : firstMass packingDensity ≤ firstMass packingDensity+1))
    (hgeom (triangleVertex packingDensity) (fun _ => by simp only [dist_self]; exact hτ.le))
  let s₀ : ConstructionStage t packingDensity τ 0 := {
    σ := fun _ => 0, R := fun _ => 1, a := firstMass packingDensity, x := x,
    σ_nonneg := fun _ => le_refl _, R_one := fun _ => le_refl _, σ_summable := summable_zero,
    a_pos := ha, mass := by simp [geometricBudget],
    referenceBounded := ⟨1,by norm_num,fun _ _ => le_refl _⟩,
    location := by
      change dist x initialPoint < 1/64 at hx
      norm_num [locationRadius,geometricBudget]
      linarith,
    triple := by
      have he : groupRadius τ 0 = τ/2 := by norm_num [groupRadius,geometricBudget]; ring
      rw [he,physicalProfile_zero]
      exact htr }
  exact sequence_of_initial hp hτ hτp hγ (hT.mono_t ht) hgeom s₀ rfl rfl

end ContinuumTemperature
end
end

end OAI
end

theorem solution : type_of% @OAI.ContinuumTemperature.exists_constructionData_oai := @OAI.ContinuumTemperature.exists_constructionData_oai

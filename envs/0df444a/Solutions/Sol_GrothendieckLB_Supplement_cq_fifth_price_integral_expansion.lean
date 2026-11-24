-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_fifth_price_integral_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:36:09.548955+00:00
-- url     : https://prove2.me/submissions/1f5a4922-c175-4b46-859c-3d9558977e54

import Theorems.Thm_GrothendieckLB_Supplement_cq_first_price_derivative
import Theorems.Thm_GrothendieckLB_Supplement_cq_mixed_price_derivative
import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open GrothendieckLB.Supplement.CQPrice Filter
open scoped Topology
namespace CQPriceExpansion

noncomputable def dpoly (p : RationalPoly) (z : ℂ) :=
  ((p.terms.map (fun e => (e.2:ℂ)*((e.1:ℂ)*z^(e.1-1)))).sum)/(p.denominator:ℂ)

private theorem dmonomials (ts : List (ℕ×ℤ)) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (ts.map (fun e => (e.2:ℂ)*w^e.1)).sum)
      ((ts.map (fun e => (e.2:ℂ)*((e.1:ℂ)*z^(e.1-1)))).sum) z := by
  induction ts with
  | nil => simpa using hasDerivAt_const z (0:ℂ)
  | cons e ts ih =>
    simp only [List.map_cons,List.sum_cons]
    exact ((hasDerivAt_pow e.1 z).const_mul (e.2:ℂ)).add ih
private theorem deval (p : RationalPoly) (z : ℂ) : HasDerivAt (eval p) (dpoly p z) z :=
  (dmonomials p.terms z).div_const _

noncomputable def form (ts : List Term) (z : ℂ) (T : ℕ → ℕ → ℂ) :=
  (ts.map (fun t => eval t.polynomial z*T t.parameterOrder t.spatialOrder)).sum

noncomputable def dform (ts : List Term) (z : ℂ) (T : ℕ → ℕ → ℂ) :=
  (ts.map (fun t =>
    let p:=t.parameterOrder
    let a:=t.spatialOrder
    dpoly t.polynomial z*T p a+eval t.polynomial z*(dpoly rho z*T (p+1) a-T p (a+1)))).sum

private theorem form_hasDerivAt (ts : List Term) (z : ℂ) (hz : ‖z‖<1)
    (hord : ∀ t∈ts, 0<t.parameterOrder+t.spatialOrder ∧ t.parameterOrder+t.spatialOrder<5)
    (step : ∀ p a : ℕ, 0<p+a → p+a<5 → ∀ z : ℂ, ‖z‖<1 →
      HasDerivAt (fun w => partialTerm w p a)
        (deriv (eval rho) z*partialTerm z (p+1) a-partialTerm z p (a+1)) z) :
    HasDerivAt (fun w => form ts w (partialTerm w)) (dform ts z (partialTerm z)) z := by
  induction ts with
  | nil => simpa [form,dform] using hasDerivAt_const z (0:ℂ)
  | cons t ts ih =>
    have h := hord t (by simp)
    have hp := step t.parameterOrder t.spatialOrder h.1 h.2 z hz
    rw [(deval rho z).deriv] at hp
    exact ((deval t.polynomial z).mul hp).add (ih fun u hu => hord u (by simp [hu]))

private noncomputable def E (g : ℂ → ℂ) (w : ℂ) := w*deriv g w
private theorem promote (F : ℂ→ℂ) (k : ℕ) (ts us : List Term)
    (prev : ∀ z : ℂ, ‖z‖<1 → (E^[k] F) z=form ts z (partialTerm z))
    (hstep : ∀ z : ℂ, ‖z‖<1 → HasDerivAt (fun w => form ts w (partialTerm w)) (dform ts z (partialTerm z)) z)
    (hcoeff : ∀ (z : ℂ) (T : ℕ → ℕ → ℂ), z*dform ts z T = form us z T) :
    ∀ z : ℂ, ‖z‖<1 → (E^[k+1] F) z=form us z (partialTerm z) := by
  intro z hz
  have heq : E^[k] F =ᶠ[𝓝 z] (fun w => form ts w (partialTerm w)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z∈Metric.ball (0:ℂ) 1 by simpa using hz)] with w hw
    exact prev w (by simpa using hw)
  rw [Function.iterate_succ_apply',E,((hstep z hz).congr_of_eventuallyEq heq).deriv,hcoeff]

private def stage1 : List Term :=
  [⟨0,1,⟨1, [(1, -1)]⟩,[]⟩,
   ⟨1,0,⟨11190724005347697, [(1, 10000000000000000), (3, -3488659974190128), (5, 139186736421605)]⟩,[]⟩]
private theorem orders1 : stage1.all (fun t => decide (0<t.parameterOrder+t.spatialOrder ∧ t.parameterOrder+t.spatialOrder<5))=true := by decide +kernel

private def stage2 : List Term :=
  [⟨0,1,⟨1, [(1, -1)]⟩,[]⟩,
   ⟨0,2,⟨1, [(2, 1)]⟩,[]⟩,
   ⟨1,0,⟨11190724005347697, [(1, 10000000000000000), (3, -10465979922570384), (5, 695933682108025)]⟩,[]⟩,
   ⟨1,1,⟨11190724005347697, [(2, -20000000000000000), (4, 6977319948380256), (6, -278373472843210)]⟩,[]⟩,
   ⟨2,0,⟨125232303763865202353853863203809, [(2, 100000000000000000000000000000000), (4, -69773199483802560000000000000000), (6, 14954483143948364563109492656384), (8, -971150392584409296321273830880), (10, 19372947595697343840310776025)]⟩,[]⟩]
private theorem orders2 : stage2.all (fun t => decide (0<t.parameterOrder+t.spatialOrder ∧ t.parameterOrder+t.spatialOrder<5))=true := by decide +kernel

private def stage3 : List Term :=
  [⟨0,1,⟨1, [(1, -1)]⟩,[]⟩,
   ⟨0,2,⟨1, [(2, 3)]⟩,[]⟩,
   ⟨0,3,⟨1, [(3, -1)]⟩,[]⟩,
   ⟨1,0,⟨11190724005347697, [(1, 10000000000000000), (3, -31397939767711152), (5, 3479668410540125)]⟩,[]⟩,
   ⟨1,1,⟨3730241335115899, [(2, -20000000000000000), (4, 13954639896760512), (6, -835120418529630)]⟩,[]⟩,
   ⟨1,2,⟨3730241335115899, [(3, 10000000000000000), (5, -3488659974190128), (7, 139186736421605)]⟩,[]⟩,
   ⟨2,0,⟨41744101254621734117951287734603, [(2, 100000000000000000000000000000000), (4, -139546398967605120000000000000000), (6, 44863449431845093689328477969152), (8, -3884601570337637185285095323520), (10, 96864737978486719201553880125)]⟩,[]⟩,
   ⟨2,1,⟨41744101254621734117951287734603, [(3, -100000000000000000000000000000000), (5, 69773199483802560000000000000000), (7, -14954483143948364563109492656384), (9, 971150392584409296321273830880), (11, -19372947595697343840310776025)]⟩,[]⟩,
   ⟨3,0,⟨1401440147975281067887239570479679510409419777873, [(3, 1000000000000000000000000000000000000000000000000), (5, -1046597992257038400000000000000000000000000000000), (7, 406878473391969436893284779691520000000000000000), (9, -71594114630681791671698175285028677993788977152), (11, 5663208683163307330735556324513508522056328960), (13, -202756880577576593562847189886900791722243600), (15, 2696457350711892504086540790341029126020125)]⟩,[]⟩]
private theorem orders3 : stage3.all (fun t => decide (0<t.parameterOrder+t.spatialOrder ∧ t.parameterOrder+t.spatialOrder<5))=true := by decide +kernel

private def stage4 : List Term :=
  [⟨0,1,⟨1, [(1, -1)]⟩,[]⟩,
   ⟨0,2,⟨1, [(2, 7)]⟩,[]⟩,
   ⟨0,3,⟨1, [(3, -6)]⟩,[]⟩,
   ⟨0,4,⟨1, [(4, 1)]⟩,[]⟩,
   ⟨1,0,⟨11190724005347697, [(1, 10000000000000000), (3, -94193819303133456), (5, 17398342052700625)]⟩,[]⟩,
   ⟨1,1,⟨11190724005347697, [(2, -140000000000000000), (4, 202342278503027424), (6, -18651022680495070)]⟩,[]⟩,
   ⟨1,2,⟨3730241335115899, [(3, 60000000000000000), (5, -34886599741901280), (7, 1948614309902470)]⟩,[]⟩,
   ⟨1,3,⟨11190724005347697, [(4, -40000000000000000), (6, 13954639896760512), (8, -556746945686420)]⟩,[]⟩,
   ⟨2,0,⟨125232303763865202353853863203809, [(2, 700000000000000000000000000000000), (4, -2023422785030274240000000000000000), (6, 953267376982475367475898037352192), (8, -109739994362038250484303942889440), (10, 3390265829247035172054385804375)]⟩,[]⟩,
   ⟨2,1,⟨41744101254621734117951287734603, [(3, -600000000000000000000000000000000), (5, 697731994838025600000000000000000), (7, -209362764015277103883532897189376), (9, 17480707066519367333782928955840), (11, -426204847105341564486837072550)]⟩,[]⟩,
   ⟨2,2,⟨41744101254621734117951287734603, [(4, 200000000000000000000000000000000), (6, -139546398967605120000000000000000), (8, 29908966287896729126218985312768), (10, -1942300785168818592642547661760), (12, 38745895191394687680621552050)]⟩,[]⟩,
   ⟨3,0,⟨467146715991760355962413190159893170136473259291, [(3, 2000000000000000000000000000000000000000000000000), (5, -3488659974190128000000000000000000000000000000000), (7, 1898766209162524038835328971893760000000000000000), (9, -429564687784090750030189051710172067962733862912), (11, 41530197009864253758727413046432395828413079040), (13, -1757226298338997144211342312353140194926111200), (15, 26964573507118925040865407903410291260201250)]⟩,[]⟩,
   ⟨3,1,⟨1401440147975281067887239570479679510409419777873, [(4, -4000000000000000000000000000000000000000000000000), (6, 4186391969028153600000000000000000000000000000000), (8, -1627513893567877747573139118766080000000000000000), (10, 286376458522727166686792701140114711975155908608), (12, -22652834732653229322942225298054034088225315840), (14, 811027522310306374251388759547603166888974400), (16, -10785829402847570016346163161364116504080500)]⟩,[]⟩,
   ⟨4,0,⟨15683129906005006528158327796014028398782414413095972969872108481, [(4, 10000000000000000000000000000000000000000000000000000000000000000), (6, -13954639896760512000000000000000000000000000000000000000000000000), (8, 7859195994996178737865695593830400000000000000000000000000000000), (10, -2281074349676626089075162712873147119751559086080000000000000000), (12, 363031695762905551376873366902942391470784736882186024695955456), (14, -31749529426652459202623109895825250520690383152547430336675840), (16, 1522557921553754148308310686449091944059041893052466262361600), (18, -37628091326157327311893987941592159797202284766594817304000), (20, 375311098545635495373559713323834200843403453737714800625)]⟩,[]⟩]
private theorem orders4 : stage4.all (fun t => decide (0<t.parameterOrder+t.spatialOrder ∧ t.parameterOrder+t.spatialOrder<5))=true := by decide +kernel

private theorem rec1 (z : ℂ) (T : ℕ → ℕ → ℂ) :
    z*dform stage1 z T = form stage2 z T := by
  norm_num [dform,form,stage1,stage2,rho,eval,dpoly] <;> ring
private theorem rec2 (z : ℂ) (T : ℕ → ℕ → ℂ) :
    z*dform stage2 z T = form stage3 z T := by
  norm_num [dform,form,stage2,stage3,rho,eval,dpoly] <;> ring
private theorem rec3 (z : ℂ) (T : ℕ → ℕ → ℂ) :
    z*dform stage3 z T = form stage4 z T := by
  norm_num [dform,form,stage3,stage4,rho,eval,dpoly] <;> ring
private theorem rec4 (z : ℂ) (T : ℕ → ℕ → ℂ) :
    z*dform stage4 z T = form terms z T := by
  norm_num [dform,form,stage4,terms,rho,eval,dpoly] <;> ring
private theorem res (F : ℂ→ℂ)
    (base : ∀ z : ℂ, ‖z‖<1 → HasDerivAt F
      (deriv (eval rho) z*partialTerm z 1 0-partialTerm z 0 1) z)
    (step : ∀ p a : ℕ, 0<p+a → p+a<5 → ∀ z : ℂ, ‖z‖<1 →
      HasDerivAt (fun w => partialTerm w p a)
        (deriv (eval rho) z*partialTerm z (p+1) a-partialTerm z p (a+1)) z) :
    ∀ z : ℂ, ‖z‖<1 → (E^[5] F) z=form terms z (partialTerm z) := by
  have h1 (z : ℂ) (hz : ‖z‖<1) : (E^[1] F) z=form stage1 z (partialTerm z) := by
    change z * deriv F z=_
    rw [(base z hz).deriv,(deval rho z).deriv]
    have basepoly (T : ℕ → ℕ → ℂ) : z*(dpoly rho z*T 1 0 - T 0 1)=form stage1 z T := by
      norm_num [form,stage1,rho,eval,dpoly] <;> ring
    exact basepoly (partialTerm z)
  have h2 := promote F 1 stage1 stage2 h1 (fun z hz => form_hasDerivAt _ z hz (fun t ht => of_decide_eq_true (List.all_eq_true.mp orders1 t ht)) step) rec1
  have h3 := promote F 2 stage2 stage3 h2 (fun z hz => form_hasDerivAt _ z hz (fun t ht => of_decide_eq_true (List.all_eq_true.mp orders2 t ht)) step) rec2
  have h4 := promote F 3 stage3 stage4 h3 (fun z hz => form_hasDerivAt _ z hz (fun t ht => of_decide_eq_true (List.all_eq_true.mp orders3 t ht)) step) rec3
  have h5 := promote F 4 stage4 terms h4 (fun z hz => form_hasDerivAt _ z hz (fun t ht => of_decide_eq_true (List.all_eq_true.mp orders4 t ht)) step) rec4
  exact h5

end CQPriceExpansion

open GrothendieckLB.Supplement

theorem solution (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t|<1 → F (t:ℂ)=(cqCorr 0.136419125 0.34101124 0.05276111 t:ℂ))
    (z : ℂ) (hz : ‖z‖<1) :
    (((fun g : ℂ → ℂ => fun w : ℂ => w * deriv g w)^[5]) F) z =
      (CQPrice.terms.map (fun t => CQPrice.eval t.polynomial z *
        CQPrice.partialTerm z t.parameterOrder t.spatialOrder)).sum :=
  CQPriceExpansion.res F (cq_first_price_derivative F hF hreal) cq_mixed_price_derivative z hz
